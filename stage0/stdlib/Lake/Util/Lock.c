// Lean compiler output
// Module: Lake.Util.Lock
// Imports: public import Init.System.IO import Init.Data.ToString.Macro
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
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
uint32_t lean_io_process_get_pid();
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "warning: waiting for prior `lake build` invocation to finish... (remove '"};
static const lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0 = (const lean_object*)&l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value;
static const lean_string_object l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' if stuck)"};
static const lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1 = (const lean_object*)&l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value;
lean_object* l_IO_sleep(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(lean_object*, uint8_t);
lean_object* lean_get_stderr();
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object*);
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object*);
static const lean_string_object l_Lake_withLockFile___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "warning: `"};
static const lean_object* l_Lake_withLockFile___redArg___lam__2___closed__0 = (const lean_object*)&l_Lake_withLockFile___redArg___lam__2___closed__0_value;
static const lean_string_object l_Lake_withLockFile___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` was deleted before the lock was released"};
static const lean_object* l_Lake_withLockFile___redArg___lam__2___closed__1 = (const lean_object*)&l_Lake_withLockFile___redArg___lam__2___closed__1_value;
lean_object* l_IO_eprintln___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_withLockFile___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_withLockFile___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_withLockFile___redArg___closed__0 = (const lean_object*)&l_Lake_withLockFile___redArg___closed__0_value;
lean_object* l_instToStringString___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_withLockFile___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringString___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_withLockFile___redArg___closed__1 = (const lean_object*)&l_Lake_withLockFile___redArg___closed__1_value;
lean_object* l_IO_FS_removeFile___boxed(lean_object*, lean_object*);
lean_object* l_EST_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 2;
x_5 = lean_io_prim_handle_mk(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_io_process_get_pid();
x_8 = lean_uint32_to_nat(x_7);
x_9 = l_Nat_reprFast(x_8);
x_10 = l_IO_FS_Handle_putStrLn(x_6, x_9);
lean_dec(x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_4; lean_object* x_10; lean_object* x_21; 
lean_inc_ref(x_1);
x_21 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_IO_FS_createDirAll(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_24);
x_10 = x_25;
goto block_20;
}
else
{
x_10 = x_23;
goto block_20;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(x_1, x_26);
x_10 = x_27;
goto block_20;
}
block_9:
{
uint32_t x_5; lean_object* x_6; uint8_t x_7; 
x_5 = 300;
x_6 = l_IO_sleep(x_5);
x_7 = 0;
x_2 = x_7;
goto _start;
}
block_20:
{
if (lean_obj_tag(x_10) == 0)
{
lean_dec_ref(x_1);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_dec_ref(x_10);
if (x_2 == 0)
{
x_4 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_get_stderr();
x_13 = ((lean_object*)(l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0));
x_14 = lean_string_append(x_13, x_1);
x_15 = ((lean_object*)(l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1));
x_16 = lean_string_append(x_14, x_15);
lean_inc_ref(x_12);
x_17 = l_IO_FS_Stream_putStrLn(x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_17);
x_18 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_12);
x_19 = lean_apply_1(x_18, lean_box(0));
if (lean_obj_tag(x_19) == 0)
{
lean_dec_ref(x_19);
x_4 = lean_box(0);
goto block_9;
}
else
{
lean_dec_ref(x_1);
return x_19;
}
}
else
{
lean_dec_ref(x_12);
lean_dec_ref(x_1);
return x_17;
}
}
}
else
{
lean_dec_ref(x_1);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_busyAcquireLockFile___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_busyAcquireLockFile(x_1);
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
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_withLockFile___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_withLockFile___redArg___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_5 = ((lean_object*)(l_Lake_withLockFile___redArg___lam__2___closed__0));
x_6 = lean_string_append(x_5, x_1);
x_7 = ((lean_object*)(l_Lake_withLockFile___redArg___lam__2___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = l_IO_eprintln___redArg(x_2, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec_ref(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_withLockFile___redArg___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
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
LEAN_EXPORT lean_object* l_Lake_withLockFile___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc_ref(x_4);
x_10 = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(x_10, 0, x_4);
lean_inc(x_3);
x_11 = lean_apply_2(x_3, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_5);
x_13 = ((lean_object*)(l_Lake_withLockFile___redArg___closed__0));
x_14 = ((lean_object*)(l_Lake_withLockFile___redArg___closed__1));
lean_inc_ref(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_15, 0, x_4);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
x_17 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_17, 0, x_4);
x_18 = lean_alloc_closure((void*)(l_EST_tryCatch___boxed), 6, 5);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, lean_box(0));
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_15);
x_19 = lean_apply_2(x_3, lean_box(0), x_18);
x_20 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_16, x_20);
x_22 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_21);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_withLockFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec_ref(x_9);
lean_inc_ref(x_6);
x_12 = lean_alloc_closure((void*)(l_Lake_busyAcquireLockFile___boxed), 2, 1);
lean_closure_set(x_12, 0, x_6);
lean_inc(x_5);
x_13 = lean_apply_2(x_5, lean_box(0), x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_7);
x_15 = ((lean_object*)(l_Lake_withLockFile___redArg___closed__0));
x_16 = ((lean_object*)(l_Lake_withLockFile___redArg___closed__1));
lean_inc_ref(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__2___boxed), 4, 2);
lean_closure_set(x_17, 0, x_6);
lean_closure_set(x_17, 1, x_16);
x_18 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_13, x_14);
x_19 = lean_alloc_closure((void*)(l_IO_FS_removeFile___boxed), 2, 1);
lean_closure_set(x_19, 0, x_6);
x_20 = lean_alloc_closure((void*)(l_EST_tryCatch___boxed), 6, 5);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
lean_closure_set(x_20, 2, lean_box(0));
lean_closure_set(x_20, 3, x_19);
lean_closure_set(x_20, 4, x_17);
x_21 = lean_apply_2(x_5, lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l_Lake_withLockFile___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_22);
x_24 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_23);
return x_24;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lock(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
