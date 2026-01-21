// Lean compiler output
// Module: Std.Internal.Async.Timer
// Imports: public import Std.Time public import Std.Internal.UV.Timer public import Std.Internal.Async.Select
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg(lean_object*);
lean_object* lean_uv_timer_next(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1;
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12;
static lean_object* l_Std_Internal_IO_Async_Sleep_wait___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4;
static lean_object* l_Std_Internal_IO_Async_Selector_sleep___closed__0;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0(lean_object*);
lean_object* lean_uv_timer_cancel(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2;
static lean_object* l_Std_Internal_IO_Async_Sleep_mk___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3;
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0(lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg___boxed(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10;
static lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18;
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7(lean_object*, lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17;
static lean_object* l_Std_Internal_IO_Async_sleep___closed__0;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24;
static lean_object* l_Std_Internal_IO_Async_Sleep_wait___closed__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_mk___lam__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_mk___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; 
x_3 = l_Std_Internal_IO_Async_Sleep_mk___closed__0;
x_11 = l_Int_toNat(x_1);
x_12 = lean_uint64_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = lean_uv_timer_mk(x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
x_4 = x_14;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_4 = x_17;
x_5 = lean_box(0);
goto block_10;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_ctor_set_tag(x_14, 0);
x_4 = x_14;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_4 = x_20;
x_5 = lean_box(0);
goto block_10;
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_mk(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_wait___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("the promise linked to the Async was dropped", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_wait___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Sleep_wait___closed__0;
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_wait___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_7 = lean_io_promise_result_opt(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_6, x_7, x_8, x_9);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_13 = lean_io_promise_result_opt(x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = lean_task_map(x_12, x_13, x_14, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_ctor_set_tag(x_3, 0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_wait(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_timer_reset(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_3 = x_10;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_reset(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_stop(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_16; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_st_ref_take(x_5);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 1;
x_8 = x_17;
goto block_15;
}
else
{
uint8_t x_18; 
x_18 = 0;
x_8 = x_18;
goto block_15;
}
block_15:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_st_ref_set(x_5, x_10);
if (x_8 == 0)
{
lean_object* x_12; 
x_12 = lean_apply_1(x_3, lean_box(0));
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_io_promise_resolve(x_13, x_6);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec_ref(x_1);
x_8 = l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_7; 
x_7 = lean_uv_timer_cancel(x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_3 = x_10;
x_4 = lean_box(0);
goto block_6;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_ctor_set_tag(x_7, 0);
x_3 = x_7;
x_4 = lean_box(0);
goto block_6;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_3 = x_13;
x_4 = lean_box(0);
goto block_6;
}
}
block_6:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__1(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2(lean_object* x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__2(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0;
x_7 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(x_5, x_1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_io_promise_result_opt(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = 0;
x_14 = l_BaseIO_chainTask___redArg(x_11, x_1, x_12, x_13);
lean_ctor_set(x_2, 0, x_14);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_io_promise_result_opt(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = 0;
x_20 = l_BaseIO_chainTask___redArg(x_17, x_1, x_18, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_13 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
x_6 = x_13;
x_7 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_6 = x_16;
x_7 = lean_box(0);
goto block_12;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_6 = x_13;
x_7 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_6 = x_19;
x_7 = lean_box(0);
goto block_12;
}
}
block_12:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_9, x_10, x_8, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__5(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_3, 0);
x_19 = lean_unbox(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_uv_timer_cancel(x_2);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_ctor_set(x_3, 0, x_21);
x_12 = x_3;
x_13 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_22);
x_12 = x_3;
x_13 = lean_box(0);
goto block_18;
}
}
else
{
lean_object* x_23; 
lean_free_object(x_3);
lean_dec(x_11);
lean_dec_ref(x_1);
x_23 = l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2;
return x_23;
}
block_18:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_unbox(x_11);
lean_dec(x_11);
x_17 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_15, x_16, x_14, x_1);
return x_17;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_32; 
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_32 = lean_unbox(x_24);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_uv_timer_cancel(x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_25 = x_35;
x_26 = lean_box(0);
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_25 = x_37;
x_26 = lean_box(0);
goto block_31;
}
}
else
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec_ref(x_1);
x_38 = l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2;
return x_38;
}
block_31:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unbox(x_24);
lean_dec(x_24);
x_30 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_28, x_29, x_27, x_1);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Sleep_selector___lam__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_IO_Promise_isResolved___redArg(x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
lean_ctor_set(x_2, 0, x_12);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_14, x_15, x_13, x_1);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_IO_Promise_isResolved___redArg(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = 0;
x_24 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_22, x_23, x_21, x_1);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__7(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_11; 
x_11 = lean_uv_timer_next(x_2);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 1);
x_4 = x_11;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_4 = x_14;
x_5 = lean_box(0);
goto block_10;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_4 = x_11;
x_5 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_4 = x_17;
x_5 = lean_box(0);
goto block_10;
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__8(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Sleep_selector___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Std_Internal_IO_Async_Sleep_selector___closed__0;
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_uv_timer_next(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_free_object(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_14 = lean_io_promise_result_opt(x_12);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = 0;
x_17 = lean_task_map(x_13, x_14, x_15, x_16);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_20 = lean_io_promise_result_opt(x_18);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 0;
x_23 = lean_task_map(x_19, x_20, x_21, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_10, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_26);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_27);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_1);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_uv_timer_next(x_29);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_34 = lean_io_promise_result_opt(x_31);
lean_dec(x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = 0;
x_37 = lean_task_map(x_33, x_34, x_35, x_36);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_32;
 lean_ctor_set_tag(x_38, 1);
}
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_40 = x_30;
} else {
 lean_dec_ref(x_30);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_39);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_40;
 lean_ctor_set_tag(x_42, 0);
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_sleep___lam__1(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_sleep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_sleep___lam__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; uint64_t x_14; uint8_t x_15; lean_object* x_16; 
x_3 = l_Std_Internal_IO_Async_sleep___closed__0;
x_4 = l_Std_Internal_IO_Async_Sleep_mk___closed__0;
x_13 = l_Int_toNat(x_1);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = lean_uv_timer_mk(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_5 = x_22;
x_6 = lean_box(0);
goto block_12;
}
}
block_12:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_4);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_10, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_sleep(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = l_Std_Internal_IO_Async_Sleep_selector(x_9);
lean_ctor_set(x_1, 0, x_10);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Std_Internal_IO_Async_Sleep_selector(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selector_sleep___lam__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Selector_sleep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; uint64_t x_14; uint8_t x_15; lean_object* x_16; 
x_3 = l_Std_Internal_IO_Async_Selector_sleep___closed__0;
x_4 = l_Std_Internal_IO_Async_Sleep_mk___closed__0;
x_13 = l_Int_toNat(x_1);
x_14 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = lean_uv_timer_mk(x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 1);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_5 = x_19;
x_6 = lean_box(0);
goto block_12;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_5 = x_16;
x_6 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_5 = x_22;
x_6 = lean_box(0);
goto block_12;
}
}
block_12:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_4);
x_11 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_10, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selector_sleep(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2;
x_3 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1;
x_4 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2;
x_3 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1;
x_4 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decide", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2;
x_3 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1;
x_4 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10;
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("optConfig", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2;
x_3 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1;
x_4 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25;
x_2 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4;
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Int_toNat(x_1);
x_4 = lean_uint64_of_nat(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = lean_uv_timer_mk(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_mk___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = l_Int_toNat(x_1);
x_5 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
x_6 = 1;
x_7 = lean_uv_timer_mk(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Interval_mk(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_7 = lean_io_promise_result_opt(x_5);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = lean_task_map(x_6, x_7, x_8, x_9);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Std_Internal_IO_Async_Sleep_wait___closed__1;
x_13 = lean_io_promise_result_opt(x_11);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = 0;
x_16 = lean_task_map(x_12, x_13, x_14, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_ctor_set_tag(x_3, 0);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_tick(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_reset(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_reset(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_stop(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_IO_Async_Sleep_mk___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_mk___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_mk___closed__0);
l_Std_Internal_IO_Async_Sleep_wait___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_wait___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_wait___closed__0);
l_Std_Internal_IO_Async_Sleep_wait___closed__1 = _init_l_Std_Internal_IO_Async_Sleep_wait___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_wait___closed__1);
l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0);
l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1);
l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0);
l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0);
l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1);
l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2 = _init_l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2);
l_Std_Internal_IO_Async_Sleep_selector___closed__0 = _init_l_Std_Internal_IO_Async_Sleep_selector___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Sleep_selector___closed__0);
l_Std_Internal_IO_Async_sleep___closed__0 = _init_l_Std_Internal_IO_Async_sleep___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_sleep___closed__0);
l_Std_Internal_IO_Async_Selector_sleep___closed__0 = _init_l_Std_Internal_IO_Async_Selector_sleep___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Selector_sleep___closed__0);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25);
l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26);
l_Std_Internal_IO_Async_Interval_mk___auto__1 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
