// Lean compiler output
// Module: Lean.Server.FileWorker.SetupFile
// Imports: Init.System.IO Lean.Server.Utils Lean.Util.LakePath Lean.LoadDynlib Lean.Server.ServerTask
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_determineLakePath(lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__0;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_io_process_child_take_stdin(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResultKind_ctorIdx(lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__4;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_toJsonModuleHeader____x40_Lean_Setup_2548614533____hygCtx___hyg_40_(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResultKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_LakeSetupFileOutput_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object*);
lean_object* lean_io_prim_handle_get_line(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_IO_asTask___redArg(lean_object*, lean_object*);
lean_object* l_Lean_fromJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_129_(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_LakeSetupFileOutput_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__8;
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__3;
lean_object* l_String_intercalate(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_load_dynlib(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
lean_object* l_Lean_Json_parse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__0;
static lean_object* l_Lean_Server_FileWorker_setupFile___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_LakeSetupFileOutput_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_LakeSetupFileOutput_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_LakeSetupFileOutput_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_io_prim_handle_get_line(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
x_11 = lean_string_dec_eq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_inc_ref(x_1);
lean_inc(x_8);
x_12 = lean_apply_2(x_1, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_3 = x_14;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_1);
lean_ctor_set(x_6, 0, x_3);
return x_6;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_6, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_6);
x_22 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
x_23 = lean_string_dec_eq(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc_ref(x_1);
lean_inc(x_20);
x_24 = lean_apply_2(x_1, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_3, x_20);
lean_dec(x_20);
x_3 = x_26;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_30 = x_24;
} else {
 lean_dec_ref(x_24);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_20);
lean_dec_ref(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_io_error_to_string(x_3);
x_5 = lean_mk_io_user_error(x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; 
x_1 = 0;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, 1, x_1);
lean_ctor_set_uint8(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("setup-file", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__3;
x_2 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--no-build", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--no-cache", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_86 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__4;
x_87 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__6;
x_88 = lean_array_push(x_87, x_3);
x_89 = lean_array_push(x_88, x_86);
if (x_85 == 2)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__7;
x_91 = lean_array_push(x_89, x_90);
x_92 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__8;
x_93 = lean_array_push(x_91, x_92);
x_7 = x_93;
x_8 = x_6;
goto block_84;
}
else
{
x_7 = x_89;
x_8 = x_6;
goto block_84;
}
block_84:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__0;
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__1;
x_13 = 1;
x_14 = 0;
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
lean_inc_ref(x_15);
x_16 = lean_io_process_spawn(x_15, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_io_process_child_take_stdin(x_9, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_toJsonModuleHeader____x40_Lean_Setup_2548614533____hygCtx___hyg_40_(x_4);
x_25 = l_Lean_Json_compress(x_24);
x_26 = l_IO_FS_Handle_putStrLn(x_22, x_25, x_21);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0;
lean_inc(x_23);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___boxed), 6, 5);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_5);
lean_closure_set(x_29, 2, x_7);
lean_closure_set(x_29, 3, x_23);
lean_closure_set(x_29, 4, x_28);
x_30 = l_Lean_Server_ServerTask_IO_asTask___redArg(x_29, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_23, 1);
x_34 = l_IO_FS_Handle_readToEnd(x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_task_get_own(x_31);
x_38 = l_IO_ofExcept___at___Lean_Server_FileWorker_runLakeSetupFile_spec__0___redArg(x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = l_Lean_Server_FileWorker_runLakeSetupFile___closed__2;
x_42 = lean_io_process_child_wait(x_41, x_23, x_40);
lean_dec(x_23);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint32_t x_50; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_string_utf8_byte_size(x_35);
x_46 = l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1(x_35, x_45, x_11);
x_47 = l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2(x_35, x_46, x_45);
x_48 = lean_string_utf8_extract(x_35, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_35);
x_49 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_49, 0, x_15);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_39);
x_50 = lean_unbox_uint32(x_44);
lean_dec(x_44);
lean_ctor_set_uint32(x_49, sizeof(void*)*3, x_50);
lean_ctor_set(x_42, 0, x_49);
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint32_t x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = lean_string_utf8_byte_size(x_35);
x_54 = l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1(x_35, x_53, x_11);
x_55 = l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2(x_35, x_54, x_53);
x_56 = lean_string_utf8_extract(x_35, x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_35);
x_57 = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(x_57, 0, x_15);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_39);
x_58 = lean_unbox_uint32(x_51);
lean_dec(x_51);
lean_ctor_set_uint32(x_57, sizeof(void*)*3, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_52);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_39);
lean_dec(x_35);
lean_dec_ref(x_15);
x_60 = !lean_is_exclusive(x_42);
if (x_60 == 0)
{
return x_42;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_42, 0);
x_62 = lean_ctor_get(x_42, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_42);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_35);
lean_dec(x_23);
lean_dec_ref(x_15);
x_64 = !lean_is_exclusive(x_38);
if (x_64 == 0)
{
return x_38;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_38, 0);
x_66 = lean_ctor_get(x_38, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_38);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_31);
lean_dec(x_23);
lean_dec_ref(x_15);
x_68 = !lean_is_exclusive(x_34);
if (x_68 == 0)
{
return x_34;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_34, 0);
x_70 = lean_ctor_get(x_34, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_34);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_23);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_72 = !lean_is_exclusive(x_26);
if (x_72 == 0)
{
return x_26;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_26, 0);
x_74 = lean_ctor_get(x_26, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_26);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_76 = !lean_is_exclusive(x_19);
if (x_76 == 0)
{
return x_19;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_19, 0);
x_78 = lean_ctor_get(x_19, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_19);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_80 = !lean_is_exclusive(x_16);
if (x_80 == 0)
{
return x_16;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_16, 0);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_16);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lean_Server_FileWorker_runLakeSetupFile_spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_runLakeSetupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResultKind_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResultKind_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_FileSetupResultKind_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_FileSetupResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_box(1);
x_9 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set(x_10, 5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*6, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_6 = lean_box(2);
x_7 = lean_box(0);
x_8 = lean_box(1);
x_9 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_9);
lean_ctor_set(x_10, 5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*6, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_3);
x_8 = lean_box(0);
x_9 = lean_box(1);
x_10 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0;
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_10);
lean_ctor_set(x_11, 5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*6, x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_FileSetupResult_ofError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_load_dynlib(x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid output from `", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`:\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nstderr:\n", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_setupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` failed:\n", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = l_System_Uri_fileUriToPath_x3f(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_3);
x_7 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_1, x_2, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Lean_determineLakePath(x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_System_FilePath_pathExists(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_3);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_1, x_2, x_15);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
lean_inc_ref(x_2);
x_20 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint32_t x_42; uint8_t x_43; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_ctor_get_uint32(x_21, sizeof(void*)*3);
x_25 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_22);
x_29 = l_Lean_Server_FileWorker_setupFile___closed__0;
x_30 = lean_array_to_list(x_28);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_27);
x_31 = l_String_intercalate(x_29, x_12);
x_42 = 0;
x_43 = lean_uint32_dec_eq(x_24, x_42);
if (x_43 == 0)
{
uint32_t x_44; uint8_t x_45; 
x_44 = 2;
x_45 = lean_uint32_dec_eq(x_24, x_44);
if (x_45 == 0)
{
uint32_t x_46; uint8_t x_47; 
x_46 = 3;
x_47 = lean_uint32_dec_eq(x_24, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = l_Lean_Server_FileWorker_setupFile___closed__4;
x_49 = lean_string_append(x_48, x_31);
lean_dec_ref(x_31);
x_50 = l_Lean_Server_FileWorker_setupFile___closed__5;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_25);
lean_dec_ref(x_25);
x_53 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_26);
lean_dec_ref(x_26);
x_56 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_1, x_2, x_55, x_23);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_57 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_1, x_2, x_23);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_57;
}
}
else
{
lean_object* x_58; 
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_58 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_1, x_2, x_23);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_inc_ref(x_25);
x_59 = l_Lean_Json_parse(x_25);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
goto block_41;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_fromJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_129_(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
goto block_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_31);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 3);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_array_get_size(x_63);
x_66 = lean_nat_dec_lt(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
x_67 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_62, x_23);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lean_nat_dec_le(x_65, x_65);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_65);
x_69 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_62, x_23);
return x_69;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_73 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0(x_63, x_71, x_72, x_70, x_23);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_62, x_74);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_62);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = l_Lean_Server_FileWorker_setupFile___closed__1;
x_33 = lean_string_append(x_32, x_31);
lean_dec_ref(x_31);
x_34 = l_Lean_Server_FileWorker_setupFile___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_25);
lean_dec_ref(x_25);
x_37 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_26);
lean_dec_ref(x_26);
x_40 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_1, x_2, x_39, x_23);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_40;
}
}
else
{
uint8_t x_80; 
lean_free_object(x_12);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_20);
if (x_80 == 0)
{
return x_20;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_20, 0);
x_82 = lean_ctor_get(x_20, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_20);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_12, 1);
lean_inc(x_84);
lean_dec(x_12);
lean_inc_ref(x_2);
x_85 = l_Lean_Server_FileWorker_runLakeSetupFile(x_1, x_10, x_8, x_2, x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint32_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint32_t x_108; uint8_t x_109; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec_ref(x_85);
x_89 = lean_ctor_get_uint32(x_86, sizeof(void*)*3);
x_90 = lean_ctor_get(x_86, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_86, 2);
lean_inc_ref(x_91);
lean_dec(x_86);
x_92 = lean_ctor_get(x_87, 1);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_87, 2);
lean_inc_ref(x_93);
lean_dec_ref(x_87);
x_94 = l_Lean_Server_FileWorker_setupFile___closed__0;
x_95 = lean_array_to_list(x_93);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_String_intercalate(x_94, x_96);
x_108 = 0;
x_109 = lean_uint32_dec_eq(x_89, x_108);
if (x_109 == 0)
{
uint32_t x_110; uint8_t x_111; 
x_110 = 2;
x_111 = lean_uint32_dec_eq(x_89, x_110);
if (x_111 == 0)
{
uint32_t x_112; uint8_t x_113; 
x_112 = 3;
x_113 = lean_uint32_dec_eq(x_89, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = l_Lean_Server_FileWorker_setupFile___closed__4;
x_115 = lean_string_append(x_114, x_97);
lean_dec_ref(x_97);
x_116 = l_Lean_Server_FileWorker_setupFile___closed__5;
x_117 = lean_string_append(x_115, x_116);
x_118 = lean_string_append(x_117, x_90);
lean_dec_ref(x_90);
x_119 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_120 = lean_string_append(x_118, x_119);
x_121 = lean_string_append(x_120, x_91);
lean_dec_ref(x_91);
x_122 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_1, x_2, x_121, x_88);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_122;
}
else
{
lean_object* x_123; 
lean_dec_ref(x_97);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
x_123 = l_Lean_Server_FileWorker_FileSetupResult_ofImportsOutOfDate(x_1, x_2, x_88);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_123;
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_97);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
x_124 = l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile(x_1, x_2, x_88);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_124;
}
}
else
{
lean_object* x_125; 
lean_inc_ref(x_90);
x_125 = l_Lean_Json_parse(x_90);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_125);
goto block_107;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l_Lean_fromJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_129_(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_dec_ref(x_127);
goto block_107;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec_ref(x_97);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_ctor_get(x_128, 3);
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_array_get_size(x_129);
x_132 = lean_nat_dec_lt(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_131);
x_133 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_128, x_88);
return x_133;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_131, x_131);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_131);
x_135 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_128, x_88);
return x_135;
}
else
{
lean_object* x_136; size_t x_137; size_t x_138; lean_object* x_139; 
x_136 = lean_box(0);
x_137 = 0;
x_138 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0(x_129, x_137, x_138, x_136, x_88);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = l_Lean_Server_FileWorker_FileSetupResult_ofSuccess(x_128, x_140);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_128);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
}
}
block_107:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = l_Lean_Server_FileWorker_setupFile___closed__1;
x_99 = lean_string_append(x_98, x_97);
lean_dec_ref(x_97);
x_100 = l_Lean_Server_FileWorker_setupFile___closed__2;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_string_append(x_101, x_90);
lean_dec_ref(x_90);
x_103 = l_Lean_Server_FileWorker_setupFile___closed__3;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_string_append(x_104, x_91);
lean_dec_ref(x_91);
x_106 = l_Lean_Server_FileWorker_FileSetupResult_ofError(x_1, x_2, x_105, x_88);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_106;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_85, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_85, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_148 = x_85;
} else {
 lean_dec_ref(x_85);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_150 = !lean_is_exclusive(x_9);
if (x_150 == 0)
{
return x_9;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_9, 0);
x_152 = lean_ctor_get(x_9, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_9);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_Server_FileWorker_setupFile_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_1);
return x_8;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Utils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_LakePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_LoadDynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_ServerTask(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SetupFile(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Utils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_LakePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LoadDynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_ServerTask(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0 = _init_l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Server_FileWorker_SetupFile_0__Lean_Server_FileWorker_runLakeSetupFile_processStderr___redArg___closed__0);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__0 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__0);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__1 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__1);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__2 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__2);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__3 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__3);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__4 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__4);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__5 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__5);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__6 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__6);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__7 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__7);
l_Lean_Server_FileWorker_runLakeSetupFile___closed__8 = _init_l_Lean_Server_FileWorker_runLakeSetupFile___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_runLakeSetupFile___closed__8);
l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0 = _init_l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_FileSetupResult_ofNoLakefile___closed__0);
l_Lean_Server_FileWorker_setupFile___closed__0 = _init_l_Lean_Server_FileWorker_setupFile___closed__0();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__0);
l_Lean_Server_FileWorker_setupFile___closed__1 = _init_l_Lean_Server_FileWorker_setupFile___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__1);
l_Lean_Server_FileWorker_setupFile___closed__2 = _init_l_Lean_Server_FileWorker_setupFile___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__2);
l_Lean_Server_FileWorker_setupFile___closed__3 = _init_l_Lean_Server_FileWorker_setupFile___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__3);
l_Lean_Server_FileWorker_setupFile___closed__4 = _init_l_Lean_Server_FileWorker_setupFile___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__4);
l_Lean_Server_FileWorker_setupFile___closed__5 = _init_l_Lean_Server_FileWorker_setupFile___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_setupFile___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
