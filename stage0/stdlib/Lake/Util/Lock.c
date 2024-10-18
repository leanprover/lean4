// Lean compiler output
// Module: Lake.Util.Lock
// Imports: Init
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
static lean_object* l_Lake_withLockFile___rarg___lambda__2___closed__2;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_EStateM_tryCatch___at_Lake_withLockFile___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object*, lean_object*);
static lean_object* l_Lake_withLockFile___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_sleep(uint32_t, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* lean_get_stderr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_withLockFile___rarg___closed__1;
static lean_object* l_Lake_busyAcquireLockFile_busyLoop___closed__2;
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_busyAcquireLockFile_busyLoop___closed__1;
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop(lean_object*, uint8_t, lean_object*);
lean_object* lean_io_process_get_pid(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EStateM_tryCatch___at_Lake_withLockFile___spec__1(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = 300;
x_5 = l_IO_sleep(x_4, x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Lake_busyAcquireLockFile_busyLoop(x_1, x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 2;
x_5 = lean_io_prim_handle_mk(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_io_process_get_pid(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unbox_uint32(x_9);
lean_dec(x_9);
x_12 = lean_uint32_to_nat(x_11);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = l_IO_FS_Handle_putStrLn(x_6, x_13, x_10);
lean_dec(x_6);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lake_busyAcquireLockFile_busyLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: waiting for prior `lake build` invocation to finish... (remove '", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lake_busyAcquireLockFile_busyLoop___closed__2() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_32; 
x_32 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_box(0);
x_34 = l_Lake_busyAcquireLockFile_busyLoop___lambda__2(x_1, x_33, x_3);
if (lean_obj_tag(x_34) == 0)
{
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_4 = x_35;
x_5 = x_36;
goto block_31;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_IO_FS_createDirAll(x_37, x_3);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lake_busyAcquireLockFile_busyLoop___lambda__2(x_1, x_39, x_40);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 0)
{
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_4 = x_42;
x_5 = x_43;
goto block_31;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_4 = x_44;
x_5 = x_45;
goto block_31;
}
}
block_31:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lake_busyAcquireLockFile_busyLoop___lambda__1(x_1, x_6, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_get_stderr(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lake_busyAcquireLockFile_busyLoop___closed__1;
x_12 = lean_string_append(x_11, x_1);
x_13 = l_Lake_busyAcquireLockFile_busyLoop___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_inc(x_9);
x_15 = l_IO_FS_Stream_putStrLn(x_9, x_14, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_apply_1(x_17, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lake_busyAcquireLockFile_busyLoop___lambda__1(x_1, x_19, x_20);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
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
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_busyAcquireLockFile_busyLoop___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile_busyLoop___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_busyAcquireLockFile_busyLoop___lambda__2(x_1, x_2, x_3);
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
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Lake_busyAcquireLockFile_busyLoop(x_1, x_3, x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_EStateM_tryCatch___at_Lake_withLockFile___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_EStateM_tryCatch___at_Lake_withLockFile___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_EStateM_tryCatch___at_Lake_withLockFile___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_withLockFile___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: `", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_withLockFile___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` was deleted before the lock was released", 42, 42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 11)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_4 = l_Lake_withLockFile___rarg___lambda__2___closed__1;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_withLockFile___rarg___lambda__2___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lake_withLockFile___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_withLockFile___rarg___lambda__3___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
lean_inc(x_3);
x_10 = lean_apply_2(x_3, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_Lake_withLockFile___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
lean_inc(x_4);
x_13 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_13, 0, x_4);
x_14 = lean_alloc_closure((void*)(l_Lake_withLockFile___rarg___lambda__2___boxed), 3, 1);
lean_closure_set(x_14, 0, x_4);
x_15 = lean_alloc_closure((void*)(l_EStateM_tryCatch___at_Lake_withLockFile___spec__1___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_apply_2(x_3, lean_box(0), x_15);
x_17 = lean_alloc_closure((void*)(l_Lake_withLockFile___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_12, x_17);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec(x_7);
x_20 = l_Lake_withLockFile___rarg___closed__1;
x_21 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_20, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_withLockFile___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_withLockFile___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_withLockFile___rarg___lambda__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___rarg___lambda__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_withLockFile___rarg___lambda__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lock(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_busyAcquireLockFile_busyLoop___closed__1 = _init_l_Lake_busyAcquireLockFile_busyLoop___closed__1();
lean_mark_persistent(l_Lake_busyAcquireLockFile_busyLoop___closed__1);
l_Lake_busyAcquireLockFile_busyLoop___closed__2 = _init_l_Lake_busyAcquireLockFile_busyLoop___closed__2();
lean_mark_persistent(l_Lake_busyAcquireLockFile_busyLoop___closed__2);
l_Lake_withLockFile___rarg___lambda__2___closed__1 = _init_l_Lake_withLockFile___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lake_withLockFile___rarg___lambda__2___closed__1);
l_Lake_withLockFile___rarg___lambda__2___closed__2 = _init_l_Lake_withLockFile___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lake_withLockFile___rarg___lambda__2___closed__2);
l_Lake_withLockFile___rarg___closed__1 = _init_l_Lake_withLockFile___rarg___closed__1();
lean_mark_persistent(l_Lake_withLockFile___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
