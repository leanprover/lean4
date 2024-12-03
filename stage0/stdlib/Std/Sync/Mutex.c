// Lean compiler output
// Module: Std.Sync.Mutex
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object*);
static lean_object* l_Std_Mutex_atomically___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_one(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_new___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Condvar_notifyOne___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_lock___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sync_Mutex_0__Std_CondvarImpl;
static lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1;
lean_object* lean_io_basemutex_new(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_notifyAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_BaseMutex_unlock___boxed(lean_object*, lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_condvar_notify_all(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__2(lean_object*, lean_object*);
lean_object* lean_io_condvar_wait(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1;
static lean_object* _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_basemutex_new(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_lock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_basemutex_lock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_BaseMutex_unlock___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_basemutex_unlock(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl() {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_new___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_condvar_new(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_wait___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_condvar_wait(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyOne___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_condvar_notify_one(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_notifyAll___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_condvar_notify_all(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1;
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_12);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_6);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__3), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_box(0);
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Condvar_waitUntil___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_instCoeOutMutexBaseMutex___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_instCoeOutMutexBaseMutex___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_instCoeOutMutexBaseMutex___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_st_mk_ref(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_basemutex_new(x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_new(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Mutex_new___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Std_Mutex_atomically___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg___lambda__3___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_2);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_16);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l_Std_Mutex_atomically___rarg___closed__1;
x_20 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Mutex_atomically___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Mutex_atomically___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___rarg___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Mutex_atomically___rarg___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Std_Condvar_wait___boxed), 3, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = lean_apply_2(x_3, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1;
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_12, x_6);
lean_dec(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_7);
x_9 = lean_apply_1(x_5, x_7);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_8);
lean_inc(x_8);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__3), 7, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_7);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_box(0);
lean_inc(x_1);
x_9 = l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_6);
x_8 = lean_apply_1(x_4, x_6);
x_9 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_BaseMutex_lock___boxed), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_2);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Std_BaseMutex_unlock___boxed), 2, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_13, x_16);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l_Std_Mutex_atomically___rarg___closed__1;
x_20 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4___rarg), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_Condvar_waitUntil___at_Std_Mutex_atomicallyOnce___spec__1___rarg), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_10, 0, x_7);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Std_Mutex_atomicallyOnce___spec__3___rarg), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, lean_box(0));
lean_closure_set(x_11, 2, lean_box(0));
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_10);
x_12 = l_Std_Mutex_atomically___at_Std_Mutex_atomicallyOnce___spec__4___rarg(x_1, x_2, x_3, x_4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_Mutex_atomicallyOnce___rarg), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Loop_forIn_loop___at_Std_Mutex_atomicallyOnce___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomicallyOnce___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Mutex_atomicallyOnce___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Mutex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl = _init_l___private_Std_Sync_Mutex_0__Std_BaseMutexImpl();
l___private_Std_Sync_Mutex_0__Std_CondvarImpl = _init_l___private_Std_Sync_Mutex_0__Std_CondvarImpl();
l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__1___closed__1);
l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Std_Condvar_waitUntil___spec__1___rarg___lambda__2___closed__1);
l_Std_Mutex_atomically___rarg___closed__1 = _init_l_Std_Mutex_atomically___rarg___closed__1();
lean_mark_persistent(l_Std_Mutex_atomically___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
