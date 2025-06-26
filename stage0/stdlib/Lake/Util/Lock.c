// Lean compiler output
// Module: Lake.Util.Lock
// Imports: Init.System.IO
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
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_withLockFile___redArg___closed__1;
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_get_stderr(lean_object*);
static lean_object* l_Lake_withLockFile___redArg___lam__2___closed__0;
lean_object* l_EStateM_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_withLockFile___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_busyAcquireLockFile_busyLoop___closed__0;
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_busyAcquireLockFile_busyLoop___closed__1;
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_process_get_pid(lean_object*);
lean_object* l_EStateM_nonBacktrackable(lean_object*);
static lean_object* l_Lake_withLockFile___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(2);
x_5 = lean_unbox(x_4);
x_6 = lean_io_prim_handle_mk(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_io_process_get_pid(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unbox_uint32(x_10);
lean_dec(x_10);
x_13 = lean_uint32_to_nat(x_12);
x_14 = l_Nat_reprFast(x_13);
x_15 = l_IO_FS_Handle_putStrLn(x_7, x_14, x_11);
lean_dec(x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lake_busyAcquireLockFile_busyLoop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: waiting for prior `lake build` invocation to finish... (remove '", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lake_busyAcquireLockFile_busyLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' if stuck)", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_12; lean_object* x_29; 
x_29 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
x_31 = l_Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_30, x_3);
x_12 = x_31;
goto block_28;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_IO_FS_createDirAll(x_32, x_3);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_34, x_35);
lean_dec(x_34);
x_12 = x_36;
goto block_28;
}
else
{
x_12 = x_33;
goto block_28;
}
}
block_11:
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = 300;
x_6 = l_IO_sleep(x_5, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
block_28:
{
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_13);
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_4 = x_14;
goto block_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_get_stderr(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_busyAcquireLockFile_busyLoop___closed__0;
x_20 = lean_string_append(x_19, x_1);
x_21 = l_Lake_busyAcquireLockFile_busyLoop___closed__1;
x_22 = lean_string_append(x_20, x_21);
lean_inc(x_17);
x_23 = l_IO_FS_Stream_putStrLn(x_17, x_22, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_apply_1(x_25, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_4 = x_27;
goto block_11;
}
else
{
return x_26;
}
}
else
{
lean_dec(x_17);
return x_23;
}
}
}
else
{
lean_dec(x_13);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_busyAcquireLockFile_busyLoop(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l_Lake_busyAcquireLockFile_busyLoop(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_busyAcquireLockFile(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_withLockFile___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: `", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_withLockFile___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` was deleted before the lock was released", 42, 42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_5 = l_Lake_withLockFile___redArg___lam__2___closed__0;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_Lake_withLockFile___redArg___lam__2___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_IO_eprintln___redArg(x_2, x_8, x_4);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_withLockFile___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_EStateM_nonBacktrackable(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lake_withLockFile___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instToStringString___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lake_withLockFile___redArg___closed__0;
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__1___boxed), 1, 0);
x_13 = l_Lake_withLockFile___redArg___closed__1;
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_13);
lean_inc(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(x_15, 0, x_4);
lean_inc(x_3);
x_16 = lean_apply_2(x_3, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_11);
x_18 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_18, 0, x_4);
x_19 = lean_alloc_closure((void*)(l_EStateM_tryCatch), 8, 7);
lean_closure_set(x_19, 0, lean_box(0));
lean_closure_set(x_19, 1, lean_box(0));
lean_closure_set(x_19, 2, lean_box(0));
lean_closure_set(x_19, 3, x_9);
lean_closure_set(x_19, 4, lean_box(0));
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_14);
x_20 = lean_apply_2(x_3, lean_box(0), x_19);
x_21 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_21);
x_23 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lake_withLockFile___redArg___closed__0;
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_13, 0, x_7);
x_14 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__1___boxed), 1, 0);
x_15 = l_Lake_withLockFile___redArg___closed__1;
lean_inc(x_6);
x_16 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_16, 0, x_6);
lean_closure_set(x_16, 1, x_15);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(x_17, 0, x_6);
lean_inc(x_5);
x_18 = lean_apply_2(x_5, lean_box(0), x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_13);
x_20 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_20, 0, x_6);
x_21 = lean_alloc_closure((void*)(l_EStateM_tryCatch), 8, 7);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, lean_box(0));
lean_closure_set(x_21, 3, x_11);
lean_closure_set(x_21, 4, lean_box(0));
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_16);
x_22 = lean_apply_2(x_5, lean_box(0), x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_19, x_23);
x_25 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_14, x_24);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_withLockFile___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_withLockFile___redArg___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_withLockFile___redArg___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_withLockFile___redArg___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_busyAcquireLockFile_busyLoop___closed__0 = _init_l_Lake_busyAcquireLockFile_busyLoop___closed__0();
lean_mark_persistent(l_Lake_busyAcquireLockFile_busyLoop___closed__0);
l_Lake_busyAcquireLockFile_busyLoop___closed__1 = _init_l_Lake_busyAcquireLockFile_busyLoop___closed__1();
lean_mark_persistent(l_Lake_busyAcquireLockFile_busyLoop___closed__1);
l_Lake_withLockFile___redArg___lam__2___closed__0 = _init_l_Lake_withLockFile___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lake_withLockFile___redArg___lam__2___closed__0);
l_Lake_withLockFile___redArg___lam__2___closed__1 = _init_l_Lake_withLockFile___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lake_withLockFile___redArg___lam__2___closed__1);
l_Lake_withLockFile___redArg___closed__0 = _init_l_Lake_withLockFile___redArg___closed__0();
lean_mark_persistent(l_Lake_withLockFile___redArg___closed__0);
l_Lake_withLockFile___redArg___closed__1 = _init_l_Lake_withLockFile___redArg___closed__1();
lean_mark_persistent(l_Lake_withLockFile___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
