// Lean compiler output
// Module: Std.Sync.Barrier
// Imports: public import Std.Sync.Mutex
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_new();
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
static lean_object* l_Std_Barrier_new___closed__0;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_condvar_notify_all(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_new___boxed(lean_object*, lean_object*);
lean_object* lean_io_condvar_wait(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Std_Barrier_new___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_new(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Barrier_new___closed__0;
x_4 = l_Std_Mutex_new___redArg(x_3);
x_5 = lean_io_condvar_new();
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_new___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Barrier_new(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_io_basemutex_lock(x_5);
x_7 = lean_apply_2(x_2, x_4, lean_box(0));
x_8 = lean_io_basemutex_unlock(x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_nat_dec_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
return x_2;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = l_Std_Barrier_wait___lam__0(x_1, x_5, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc_ref(x_1);
lean_inc(x_5);
x_7 = lean_apply_2(x_1, x_5, lean_box(0));
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_io_condvar_wait(x_2, x_3);
goto _start;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(x_3, x_1, x_2, x_6, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_st_ref_take(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_11);
x_12 = lean_st_ref_set(x_4, x_7);
x_13 = lean_st_ref_get(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_nat_dec_lt(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_16 = lean_st_ref_take(x_4);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_add(x_18, x_10);
lean_dec(x_18);
lean_ctor_set(x_16, 1, x_21);
lean_ctor_set(x_16, 0, x_20);
x_22 = lean_st_ref_set(x_4, x_16);
lean_dec(x_4);
x_23 = lean_io_condvar_notify_all(x_2);
x_24 = 1;
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_add(x_25, x_10);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_st_ref_set(x_4, x_28);
lean_dec(x_4);
x_30 = lean_io_condvar_notify_all(x_2);
x_31 = 1;
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_ctor_get(x_3, 1);
x_34 = lean_box(x_15);
x_35 = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__0___boxed), 4, 2);
lean_closure_set(x_35, 0, x_32);
lean_closure_set(x_35, 1, x_34);
x_36 = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(x_2, x_33, x_35, x_4);
x_37 = 0;
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_38, x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = lean_st_ref_set(x_4, x_42);
x_44 = lean_st_ref_get(x_4);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_nat_dec_lt(x_45, x_1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_6);
x_47 = lean_st_ref_take(x_4);
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
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_add(x_48, x_40);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_st_ref_set(x_4, x_52);
lean_dec(x_4);
x_54 = lean_io_condvar_notify_all(x_2);
x_55 = 1;
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_dec(x_6);
x_57 = lean_ctor_get(x_3, 1);
x_58 = lean_box(x_46);
x_59 = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__0___boxed), 4, 2);
lean_closure_set(x_59, 0, x_56);
lean_closure_set(x_59, 1, x_58);
x_60 = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(x_2, x_57, x_59, x_4);
x_61 = 0;
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Std_Barrier_wait___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_Barrier_wait(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec_ref(x_1);
lean_inc_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_Std_Barrier_wait___lam__1___boxed), 5, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_3);
x_7 = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(x_3, x_6);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Barrier_wait___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Barrier_wait(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Barrier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Barrier_new___closed__0 = _init_l_Std_Barrier_new___closed__0();
lean_mark_persistent(l_Std_Barrier_new___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
