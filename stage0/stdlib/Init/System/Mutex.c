// Lean compiler output
// Module: Init.System.Mutex
// Imports: Init.System.IO Init.Control.StateRef
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
lean_object* lean_io_basemutex_new(lean_object*);
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* lean_io_condvar_new(lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_notifyAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Mutex_0__IO_BaseMutexImpl;
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_BaseMutex_unlock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_BaseMutex_new___boxed(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_one(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Mutex_0__IO_CondvarImpl;
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_BaseMutex_lock___boxed(lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Loop_forIn_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_notifyOne___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_condvar_wait(lean_object*, lean_object*, lean_object*);
static lean_object* l_IO_Mutex_atomicallyOnce___redArg___closed__0;
LEAN_EXPORT lean_object* l_IO_Mutex_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_new___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_all(lean_object*, lean_object*);
static lean_object* _init_l___private_Init_System_Mutex_0__IO_BaseMutexImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_IO_BaseMutex_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_basemutex_new(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_BaseMutex_lock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_basemutex_lock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_BaseMutex_unlock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_basemutex_unlock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_System_Mutex_0__IO_CondvarImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_condvar_new(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_condvar_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_notifyOne___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_condvar_notify_one(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_notifyAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_condvar_notify_all(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_IO_Condvar_wait___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_6);
x_13 = lean_apply_2(x_7, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_IO_Condvar_waitUntil___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_8);
lean_inc(x_8);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_IO_Condvar_waitUntil___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_9);
lean_closure_set(x_11, 6, x_8);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_IO_Condvar_waitUntil___redArg___lam__2___boxed), 5, 3);
lean_closure_set(x_12, 0, x_7);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_IO_Condvar_waitUntil___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_9);
x_14 = l_Lean_Loop_forIn_loop___redArg(x_1, x_12, x_9);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_14, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_IO_Condvar_waitUntil___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Condvar_waitUntil___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_IO_Condvar_waitUntil___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_Condvar_waitUntil___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_Condvar_waitUntil___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Condvar_waitUntil___redArg___lam__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IO_instCoeOutMutexBaseMutex___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_instCoeOutMutexBaseMutex___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_instCoeOutMutexBaseMutex___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_new___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_io_basemutex_new(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_io_basemutex_new(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_15);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_new(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Mutex_new___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_closure((void*)(l_IO_Mutex_atomically___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_5);
lean_closure_set(x_12, 1, x_9);
x_13 = lean_alloc_closure((void*)(l_IO_Mutex_atomically___redArg___lam__1___boxed), 1, 0);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_IO_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(x_14, 0, x_10);
lean_inc(x_2);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_12);
x_17 = lean_alloc_closure((void*)(l_IO_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(x_17, 0, x_10);
x_18 = lean_apply_2(x_2, lean_box(0), x_17);
x_19 = lean_alloc_closure((void*)(l_IO_Mutex_atomically___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_19);
x_21 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_13, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_IO_Mutex_atomically___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Mutex_atomically___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_Mutex_atomically___redArg___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomically___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_Mutex_atomically___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_IO_Mutex_atomicallyOnce___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_8 = l_ReaderT_instMonad___redArg(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_IO_Mutex_atomicallyOnce___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_10, 0, x_7);
x_11 = l_IO_Mutex_atomicallyOnce___redArg___closed__0;
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
x_13 = lean_alloc_closure((void*)(l_liftM), 5, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_12);
x_14 = l_IO_Condvar_waitUntil___redArg(x_8, x_13, x_5, x_9, x_6);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, lean_box(0));
lean_closure_set(x_15, 4, lean_box(0));
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_10);
x_16 = l_IO_Mutex_atomically___redArg(x_1, x_2, x_3, x_4, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_IO_Mutex_atomicallyOnce___redArg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_IO_Mutex_atomicallyOnce___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_Mutex_atomicallyOnce___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Mutex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_System_Mutex_0__IO_BaseMutexImpl = _init_l___private_Init_System_Mutex_0__IO_BaseMutexImpl();
l___private_Init_System_Mutex_0__IO_CondvarImpl = _init_l___private_Init_System_Mutex_0__IO_CondvarImpl();
l_IO_Mutex_atomicallyOnce___redArg___closed__0 = _init_l_IO_Mutex_atomicallyOnce___redArg___closed__0();
lean_mark_persistent(l_IO_Mutex_atomicallyOnce___redArg___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
