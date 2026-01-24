// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lake.Util.Log import Lake.Config.Dynlib import Lake.Util.Proc import Lake.Util.NativeLib import Lake.Util.FilePath import Lake.Util.IO import Init.Data.String.Search
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
static lean_object* l_Lake_tar___closed__1;
static lean_object* l_Lake_download___closed__1;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__8;
static lean_object* l_Lake_compileSharedLib___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__9;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__5;
static lean_object* l_Lake_compileLeanModule___closed__6;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_remove_file(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__13;
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_compileLeanModule_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0;
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
static lean_object* l_Lake_tar___closed__10;
lean_object* lean_io_getenv(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lake_compileLeanModule___closed__5;
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
static lean_object* l_Lake_untar___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
static lean_object* l_Lake_compileLeanModule___closed__17;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__11;
lean_object* l_Lake_createParentDirs(lean_object*);
static lean_object* l_Lake_tar___closed__4;
static lean_object* l_Lake_download___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__7;
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lam__0___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_removeFileIfExists(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
static lean_object* l_Lake_tar___closed__8;
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__9;
static lean_object* l_Lake_compileLeanModule___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__0;
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__3;
static lean_object* l_Lake_compileSharedLib___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__15;
static lean_object* l_Lake_download___closed__4;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
static lean_object* l_Lake_compileLeanModule___closed__16;
static lean_object* l_Lake_untar___closed__2;
static lean_object* l_Lake_mkArgs___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_compileO___closed__0;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__1;
static lean_object* l_Lake_compileSharedLib___closed__3;
static lean_object* l_Lake_compileStaticLib___closed__0;
static lean_object* l_Lake_tar___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__6;
static lean_object* l_Lake_compileO___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__14;
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__7;
static lean_object* l_Lake_compileLeanModule___closed__4;
static lean_object* l_Lake_compileLeanModule___closed__12;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_compileO___closed__2;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__3;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkArgs___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__8;
static lean_object* l_Lake_mkArgs___closed__1;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__3;
static lean_object* l_Lake_download___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_String_Slice_positions(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
static lean_object* l_Lake_download___closed__2;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__10;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_tar___closed__7;
static lean_object* l_Lake_untar___closed__1;
static lean_object* l_Lake_compileO___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__3;
static lean_object* l_Lake_tar___closed__9;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__1;
static lean_object* _init_l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0() {
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
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_compileLeanModule_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_compileLeanModule_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileLeanModule___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean exited with code ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderr:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_string_utf8_byte_size(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_25 = l_Lake_compileLeanModule___lam__0___closed__1;
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_22);
x_27 = l_String_Slice_trimAscii(x_26);
lean_dec_ref(x_26);
x_28 = l_String_Slice_toString(x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_4, x_31);
x_6 = x_32;
x_7 = lean_box(0);
goto block_21;
}
else
{
lean_dec_ref(x_2);
x_6 = x_4;
x_7 = lean_box(0);
goto block_21;
}
block_21:
{
uint32_t x_8; uint8_t x_9; 
x_8 = 0;
x_9 = lean_uint32_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lake_compileLeanModule___lam__0___closed__0;
x_11 = lean_uint32_to_nat(x_1);
x_12 = l_Nat_reprFast(x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec_ref(x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_6);
x_17 = lean_array_push(x_6, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_compileLeanModule___lam__0(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = l_Lake_mkRelPathString(x_3);
lean_ctor_set(x_11, 0, x_17);
x_18 = l_Lake_LogEntry_ofSerialMessage(x_1);
x_19 = lean_array_push(x_5, x_18);
x_7 = x_19;
x_8 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 2);
x_22 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
x_23 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 1);
x_24 = lean_ctor_get(x_11, 3);
x_25 = lean_ctor_get(x_11, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_26 = l_Lake_mkRelPathString(x_3);
x_27 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
lean_ctor_set(x_27, 2, x_21);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 2, x_12);
lean_ctor_set(x_1, 0, x_27);
x_28 = l_Lake_LogEntry_ofSerialMessage(x_1);
x_29 = lean_array_push(x_5, x_28);
x_7 = x_29;
x_8 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_11, 2);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
x_34 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 1);
x_35 = lean_ctor_get(x_11, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_11, 4);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
x_38 = l_Lake_mkRelPathString(x_3);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 5, 3);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*5, x_33);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 1, x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*5 + 2, x_12);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
x_41 = l_Lake_LogEntry_ofSerialMessage(x_40);
x_42 = lean_array_push(x_5, x_41);
x_7 = x_42;
x_8 = lean_box(0);
goto block_10;
}
}
else
{
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = x_5;
x_8 = lean_box(0);
goto block_10;
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_6);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_6, 0);
x_62 = lean_ctor_get(x_6, 1);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
x_65 = lean_nat_sub(x_64, x_63);
x_66 = lean_nat_dec_eq(x_62, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint32_t x_68; uint8_t x_69; 
x_67 = lean_string_utf8_next_fast(x_4, x_62);
x_68 = lean_string_utf8_get_fast(x_4, x_62);
x_69 = lean_uint32_dec_eq(x_68, x_2);
if (x_69 == 0)
{
lean_dec(x_62);
lean_ctor_set(x_6, 1, x_67);
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_inc_ref(x_3);
x_71 = l_String_Slice_slice_x21(x_3, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_ctor_set(x_6, 1, x_67);
lean_ctor_set(x_6, 0, x_67);
x_72 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
lean_dec_ref(x_71);
x_36 = x_6;
x_37 = x_72;
x_38 = x_73;
x_39 = x_74;
x_40 = x_8;
x_41 = lean_box(0);
goto block_59;
}
}
else
{
lean_object* x_75; 
lean_free_object(x_6);
lean_dec(x_62);
x_75 = lean_box(1);
lean_inc(x_5);
lean_inc_ref(x_4);
x_36 = x_75;
x_37 = x_4;
x_38 = x_61;
x_39 = x_5;
x_40 = x_8;
x_41 = lean_box(0);
goto block_59;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_6, 0);
x_77 = lean_ctor_get(x_6, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_6);
x_78 = lean_ctor_get(x_3, 1);
x_79 = lean_ctor_get(x_3, 2);
x_80 = lean_nat_sub(x_79, x_78);
x_81 = lean_nat_dec_eq(x_77, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint32_t x_83; uint8_t x_84; 
x_82 = lean_string_utf8_next_fast(x_4, x_77);
x_83 = lean_string_utf8_get_fast(x_4, x_77);
x_84 = lean_uint32_dec_eq(x_83, x_2);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_77);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_82);
x_6 = x_85;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_inc_ref(x_3);
x_87 = l_String_Slice_slice_x21(x_3, x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_82);
x_89 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
lean_dec_ref(x_87);
x_36 = x_88;
x_37 = x_89;
x_38 = x_90;
x_39 = x_91;
x_40 = x_8;
x_41 = lean_box(0);
goto block_59;
}
}
else
{
lean_object* x_92; 
lean_dec(x_77);
x_92 = lean_box(1);
lean_inc(x_5);
lean_inc_ref(x_4);
x_36 = x_92;
x_37 = x_4;
x_38 = x_76;
x_39 = x_5;
x_40 = x_8;
x_41 = lean_box(0);
goto block_59;
}
}
}
else
{
lean_object* x_93; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_7);
lean_ctor_set(x_93, 1, x_8);
return x_93;
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_string_append(x_7, x_11);
lean_dec_ref(x_11);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0;
x_16 = lean_string_append(x_14, x_15);
x_6 = x_12;
x_7 = x_16;
x_8 = x_13;
goto _start;
}
block_29:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_string_utf8_byte_size(x_7);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
if (x_25 == 0)
{
x_10 = lean_box(0);
x_11 = x_19;
x_12 = x_21;
x_13 = x_22;
goto block_18;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_string_utf8_byte_size(x_19);
x_27 = lean_nat_dec_eq(x_26, x_24);
if (x_27 == 0)
{
x_10 = lean_box(0);
x_11 = x_19;
x_12 = x_21;
x_13 = x_22;
goto block_18;
}
else
{
lean_dec_ref(x_19);
x_6 = x_21;
x_8 = x_22;
goto _start;
}
}
}
block_35:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_6 = x_30;
x_7 = x_32;
x_8 = x_33;
goto _start;
}
else
{
lean_dec(x_30);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_31;
}
}
block_59:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_string_utf8_extract(x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_42);
x_43 = l_Lean_Json_parse(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_dec_ref(x_43);
x_19 = x_42;
x_20 = lean_box(0);
x_21 = x_36;
x_22 = x_40;
goto block_29;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_instFromJsonSerialMessage_fromJson(x_44);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_string_utf8_byte_size(x_7);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_eq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
x_51 = lean_string_append(x_50, x_7);
x_52 = 1;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_box(0);
x_55 = lean_array_push(x_40, x_53);
lean_inc_ref(x_1);
x_56 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(x_46, x_7, x_1, x_54, x_55);
x_30 = x_36;
x_31 = x_56;
goto block_35;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_box(0);
lean_inc_ref(x_1);
x_58 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___lam__0(x_46, x_7, x_1, x_57, x_40);
x_30 = x_36;
x_31 = x_58;
goto block_35;
}
}
else
{
lean_dec_ref(x_45);
x_19 = x_42;
x_20 = lean_box(0);
x_21 = x_36;
x_22 = x_40;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint32_t x_10; lean_object* x_11; 
x_10 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_11 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--setup", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__0;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--json", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to execute '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-b", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__10;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-c", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__12;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-i", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__14;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-o", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__16;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_16; lean_object* x_17; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_216; 
x_164 = lean_ctor_get(x_5, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_5, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_5, 6);
lean_inc(x_166);
x_167 = lean_ctor_get(x_5, 7);
lean_inc(x_167);
lean_dec_ref(x_5);
x_216 = lean_array_push(x_6, x_1);
if (lean_obj_tag(x_164) == 1)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_164, 0);
lean_inc(x_217);
lean_dec_ref(x_164);
lean_inc(x_217);
x_218 = l_Lake_createParentDirs(x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_218);
x_219 = l_Lake_compileLeanModule___closed__17;
x_220 = lean_array_push(x_219, x_217);
x_221 = l_Array_append___redArg(x_216, x_220);
lean_dec_ref(x_220);
x_200 = x_221;
x_201 = x_9;
x_202 = lean_box(0);
goto block_215;
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_222 = lean_ctor_get(x_218, 0);
lean_inc(x_222);
lean_dec_ref(x_218);
x_223 = lean_io_error_to_string(x_222);
x_224 = 3;
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_224);
x_226 = lean_array_get_size(x_9);
x_227 = lean_array_push(x_9, x_225);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
else
{
lean_dec(x_164);
x_200 = x_216;
x_201 = x_9;
x_202 = lean_box(0);
goto block_215;
}
block_15:
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_19:
{
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_11 = x_16;
x_12 = x_18;
x_13 = lean_box(0);
goto block_15;
}
}
block_163:
{
lean_object* x_23; 
lean_inc_ref(x_4);
x_23 = l_Lake_createParentDirs(x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_23);
x_24 = l_Lean_instToJsonModuleSetup_toJson(x_3);
x_25 = lean_unsigned_to_nat(80u);
x_26 = l_Lean_Json_pretty(x_24, x_25);
x_27 = l_IO_FS_writeFile(x_4, x_26);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = l_Lake_compileLeanModule___closed__2;
x_31 = lean_array_push(x_30, x_4);
x_32 = l_Array_append___redArg(x_20, x_31);
lean_dec_ref(x_31);
x_33 = l_Lake_compileLeanModule___closed__3;
x_34 = lean_array_push(x_32, x_33);
x_35 = l_Lake_compileLeanModule___closed__4;
x_36 = lean_box(0);
x_37 = l_Lake_compileLeanModule___closed__5;
x_38 = l_System_SearchPath_toString(x_7);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_27);
x_40 = l_Lake_compileLeanModule___closed__6;
x_41 = lean_array_push(x_40, x_39);
x_42 = 1;
x_43 = 0;
lean_inc_ref(x_8);
x_44 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 3, x_36);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*5, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*5 + 1, x_43);
x_45 = lean_array_get_size(x_21);
lean_inc_ref(x_44);
x_46 = l_Lake_mkCmdLog(x_44);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_array_push(x_21, x_48);
x_50 = l_IO_Process_output(x_44, x_36);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec_ref(x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get_uint32(x_51, sizeof(void*)*2);
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_54);
lean_dec(x_51);
x_55 = lean_string_utf8_byte_size(x_53);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_eq(x_55, x_56);
if (x_57 == 0)
{
uint32_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = 10;
lean_inc_ref(x_53);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_55);
x_60 = l_Lake_compileLeanModule___closed__7;
x_61 = l_String_Slice_split___at___00Lake_compileLeanModule_spec__0(x_59);
x_62 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(x_2, x_58, x_59, x_53, x_55, x_61, x_60, x_49);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_string_utf8_byte_size(x_63);
x_66 = lean_nat_dec_eq(x_65, x_56);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
x_68 = lean_string_append(x_67, x_63);
lean_dec(x_63);
x_69 = 1;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_box(0);
x_72 = lean_array_push(x_64, x_70);
x_73 = l_Lake_compileLeanModule___lam__0(x_52, x_54, x_71, x_72);
x_16 = x_45;
x_17 = x_73;
goto block_19;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_63);
x_74 = lean_box(0);
x_75 = l_Lake_compileLeanModule___lam__0(x_52, x_54, x_74, x_64);
x_16 = x_45;
x_17 = x_75;
goto block_19;
}
}
else
{
lean_object* x_76; 
lean_dec_ref(x_54);
x_76 = lean_ctor_get(x_62, 1);
lean_inc(x_76);
lean_dec_ref(x_62);
x_11 = x_45;
x_12 = x_76;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_53);
lean_dec_ref(x_2);
x_77 = lean_box(0);
x_78 = l_Lake_compileLeanModule___lam__0(x_52, x_54, x_77, x_49);
x_16 = x_45;
x_17 = x_78;
goto block_19;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_2);
x_79 = lean_ctor_get(x_50, 0);
lean_inc(x_79);
lean_dec_ref(x_50);
x_80 = l_Lake_compileLeanModule___closed__8;
x_81 = lean_string_append(x_80, x_8);
lean_dec_ref(x_8);
x_82 = l_Lake_compileLeanModule___closed__9;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_io_error_to_string(x_79);
x_85 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_push(x_49, x_87);
x_11 = x_45;
x_12 = x_88;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_27);
x_89 = l_Lake_compileLeanModule___closed__2;
x_90 = lean_array_push(x_89, x_4);
x_91 = l_Array_append___redArg(x_20, x_90);
lean_dec_ref(x_90);
x_92 = l_Lake_compileLeanModule___closed__3;
x_93 = lean_array_push(x_91, x_92);
x_94 = l_Lake_compileLeanModule___closed__4;
x_95 = lean_box(0);
x_96 = l_Lake_compileLeanModule___closed__5;
x_97 = l_System_SearchPath_toString(x_7);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lake_compileLeanModule___closed__6;
x_101 = lean_array_push(x_100, x_99);
x_102 = 1;
x_103 = 0;
lean_inc_ref(x_8);
x_104 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_8);
lean_ctor_set(x_104, 2, x_93);
lean_ctor_set(x_104, 3, x_95);
lean_ctor_set(x_104, 4, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*5, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*5 + 1, x_103);
x_105 = lean_array_get_size(x_21);
lean_inc_ref(x_104);
x_106 = l_Lake_mkCmdLog(x_104);
x_107 = 0;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_push(x_21, x_108);
x_110 = l_IO_Process_output(x_104, x_95);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint32_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec_ref(x_8);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_ctor_get_uint32(x_111, sizeof(void*)*2);
x_113 = lean_ctor_get(x_111, 0);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc_ref(x_114);
lean_dec(x_111);
x_115 = lean_string_utf8_byte_size(x_113);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_dec_eq(x_115, x_116);
if (x_117 == 0)
{
uint32_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = 10;
lean_inc_ref(x_113);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_116);
lean_ctor_set(x_119, 2, x_115);
x_120 = l_Lake_compileLeanModule___closed__7;
x_121 = l_String_Slice_split___at___00Lake_compileLeanModule_spec__0(x_119);
x_122 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(x_2, x_118, x_119, x_113, x_115, x_121, x_120, x_109);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec_ref(x_122);
x_125 = lean_string_utf8_byte_size(x_123);
x_126 = lean_nat_dec_eq(x_125, x_116);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1;
x_128 = lean_string_append(x_127, x_123);
lean_dec(x_123);
x_129 = 1;
x_130 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_129);
x_131 = lean_box(0);
x_132 = lean_array_push(x_124, x_130);
x_133 = l_Lake_compileLeanModule___lam__0(x_112, x_114, x_131, x_132);
x_16 = x_105;
x_17 = x_133;
goto block_19;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_123);
x_134 = lean_box(0);
x_135 = l_Lake_compileLeanModule___lam__0(x_112, x_114, x_134, x_124);
x_16 = x_105;
x_17 = x_135;
goto block_19;
}
}
else
{
lean_object* x_136; 
lean_dec_ref(x_114);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_dec_ref(x_122);
x_11 = x_105;
x_12 = x_136;
x_13 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_113);
lean_dec_ref(x_2);
x_137 = lean_box(0);
x_138 = l_Lake_compileLeanModule___lam__0(x_112, x_114, x_137, x_109);
x_16 = x_105;
x_17 = x_138;
goto block_19;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_2);
x_139 = lean_ctor_get(x_110, 0);
lean_inc(x_139);
lean_dec_ref(x_110);
x_140 = l_Lake_compileLeanModule___closed__8;
x_141 = lean_string_append(x_140, x_8);
lean_dec_ref(x_8);
x_142 = l_Lake_compileLeanModule___closed__9;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_io_error_to_string(x_139);
x_145 = lean_string_append(x_143, x_144);
lean_dec_ref(x_144);
x_146 = 3;
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_array_push(x_109, x_147);
x_11 = x_105;
x_12 = x_148;
x_13 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_20);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_149 = lean_ctor_get(x_27, 0);
lean_inc(x_149);
lean_dec_ref(x_27);
x_150 = lean_io_error_to_string(x_149);
x_151 = 3;
x_152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*1, x_151);
x_153 = lean_array_get_size(x_21);
x_154 = lean_array_push(x_21, x_152);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_20);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_23, 0);
lean_inc(x_156);
lean_dec_ref(x_23);
x_157 = lean_io_error_to_string(x_156);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_get_size(x_21);
x_161 = lean_array_push(x_21, x_159);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
block_183:
{
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
lean_dec_ref(x_167);
lean_inc(x_171);
x_172 = l_Lake_createParentDirs(x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec_ref(x_172);
x_173 = l_Lake_compileLeanModule___closed__11;
x_174 = lean_array_push(x_173, x_171);
x_175 = l_Array_append___redArg(x_168, x_174);
lean_dec_ref(x_174);
x_20 = x_175;
x_21 = x_169;
x_22 = lean_box(0);
goto block_163;
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_171);
lean_dec_ref(x_168);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
lean_dec_ref(x_172);
x_177 = lean_io_error_to_string(x_176);
x_178 = 3;
x_179 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_178);
x_180 = lean_array_get_size(x_169);
x_181 = lean_array_push(x_169, x_179);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_dec(x_167);
x_20 = x_168;
x_21 = x_169;
x_22 = lean_box(0);
goto block_163;
}
}
block_199:
{
if (lean_obj_tag(x_166) == 1)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_166, 0);
lean_inc(x_187);
lean_dec_ref(x_166);
lean_inc(x_187);
x_188 = l_Lake_createParentDirs(x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_188);
x_189 = l_Lake_compileLeanModule___closed__13;
x_190 = lean_array_push(x_189, x_187);
x_191 = l_Array_append___redArg(x_184, x_190);
lean_dec_ref(x_190);
x_168 = x_191;
x_169 = x_185;
x_170 = lean_box(0);
goto block_183;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_187);
lean_dec_ref(x_184);
lean_dec(x_167);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
lean_dec_ref(x_188);
x_193 = lean_io_error_to_string(x_192);
x_194 = 3;
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = lean_array_get_size(x_185);
x_197 = lean_array_push(x_185, x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
else
{
lean_dec(x_166);
x_168 = x_184;
x_169 = x_185;
x_170 = lean_box(0);
goto block_183;
}
}
block_215:
{
if (lean_obj_tag(x_165) == 1)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_165, 0);
lean_inc(x_203);
lean_dec_ref(x_165);
lean_inc(x_203);
x_204 = l_Lake_createParentDirs(x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_204);
x_205 = l_Lake_compileLeanModule___closed__15;
x_206 = lean_array_push(x_205, x_203);
x_207 = l_Array_append___redArg(x_200, x_206);
lean_dec_ref(x_206);
x_184 = x_207;
x_185 = x_201;
x_186 = lean_box(0);
goto block_199;
}
else
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_203);
lean_dec_ref(x_200);
lean_dec(x_167);
lean_dec(x_166);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_208 = lean_ctor_get(x_204, 0);
lean_inc(x_208);
lean_dec_ref(x_204);
x_209 = lean_io_error_to_string(x_208);
x_210 = 3;
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_210);
x_212 = lean_array_get_size(x_201);
x_213 = lean_array_push(x_201, x_211);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_dec(x_165);
x_184 = x_200;
x_185 = x_201;
x_186 = lean_box(0);
goto block_199;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_compileLeanModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_9, x_10, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint32_t x_14; lean_object* x_15; 
x_14 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_4);
return x_15;
}
}
static lean_object* _init_l_Lake_compileO___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__12;
x_2 = l_Lake_compileO___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileO___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__16;
x_2 = l_Lake_compileO___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileO___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_7);
x_8 = l_Lake_compileLeanModule___closed__4;
x_9 = l_Lake_compileO___closed__2;
x_10 = lean_array_push(x_9, x_1);
x_11 = lean_array_push(x_10, x_2);
x_12 = l_Array_append___redArg(x_11, x_3);
x_13 = lean_box(0);
x_14 = l_Lake_compileO___closed__3;
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_4);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_14);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = l_Lake_proc(x_17, x_16, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
lean_dec_ref(x_7);
x_20 = lean_io_error_to_string(x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_5);
x_24 = lean_array_push(x_5, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_16; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = 92;
x_16 = lean_uint32_dec_eq(x_10, x_11);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 34;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_string_push(x_4, x_10);
x_3 = x_9;
x_4 = x_19;
goto _start;
}
else
{
goto block_15;
}
}
else
{
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_string_push(x_4, x_11);
x_13 = lean_string_push(x_12, x_10);
x_3 = x_9;
x_4 = x_13;
goto _start;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = l_Lake_compileLeanModule___closed__7;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_9);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_String_Slice_positions(x_13);
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(x_13, x_9, x_14, x_10);
lean_dec(x_9);
lean_dec_ref(x_13);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0;
x_17 = lean_string_append(x_16, x_15);
lean_dec_ref(x_15);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_io_prim_handle_put_str(x_1, x_19);
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_3 = x_23;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec_ref(x_20);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_6);
x_30 = lean_array_push(x_6, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_6);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rsp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = l_System_Platform_isWindows;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; uint8_t x_24; lean_object* x_25; 
x_7 = l_Lake_mkArgs___closed__0;
x_8 = l_System_FilePath_addExtension(x_1, x_7);
x_24 = 1;
x_25 = lean_io_prim_handle_mk(x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_get_size(x_2);
x_29 = lean_nat_dec_lt(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_2);
x_9 = x_3;
x_10 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_2);
x_9 = x_3;
x_10 = lean_box(0);
goto block_16;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_28);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(x_26, x_2, x_32, x_33, x_30, x_3);
lean_dec_ref(x_2);
lean_dec(x_26);
x_17 = x_34;
goto block_23;
}
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_28);
x_37 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1(x_26, x_2, x_35, x_36, x_30, x_3);
lean_dec_ref(x_2);
lean_dec(x_26);
x_17 = x_37;
goto block_23;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_25, 0);
lean_inc(x_38);
lean_dec_ref(x_25);
x_39 = lean_io_error_to_string(x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_3);
x_43 = lean_array_push(x_3, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
block_16:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lake_mkArgs___closed__1;
x_12 = lean_string_append(x_11, x_8);
lean_dec_ref(x_8);
x_13 = l_Lake_mkArgs___closed__2;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
block_23:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_9 = x_18;
x_10 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_19; 
lean_dec_ref(x_8);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_mkArgs(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lake_mkArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcs", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileStaticLib___closed__0;
x_2 = l_Lake_mkArgs___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--thin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileStaticLib___closed__2;
x_2 = l_Lake_compileStaticLib___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc_ref(x_1);
x_7 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec_ref(x_7);
x_8 = l_Lake_removeFileIfExists(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
lean_dec_ref(x_8);
x_9 = l_Lake_compileStaticLib___closed__1;
x_10 = 1;
if (x_4 == 0)
{
x_11 = x_9;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = l_Lake_compileStaticLib___closed__3;
x_11 = x_31;
goto block_30;
}
block_30:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_size(x_2);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lake_compileStaticLib_spec__0(x_12, x_13, x_2);
lean_inc_ref(x_1);
x_15 = l_Lake_mkArgs(x_1, x_14, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = lean_array_push(x_11, x_1);
x_19 = l_Array_append___redArg(x_18, x_16);
lean_dec(x_16);
x_20 = l_Lake_compileLeanModule___closed__4;
x_21 = lean_box(0);
x_22 = l_Lake_compileO___closed__3;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_23);
x_25 = l_Lake_proc(x_24, x_23, x_17);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec_ref(x_11);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
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
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec_ref(x_8);
x_33 = lean_io_error_to_string(x_32);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_5);
x_37 = lean_array_push(x_5, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
lean_dec_ref(x_7);
x_40 = lean_io_error_to_string(x_39);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_5);
x_44 = lean_array_push(x_5, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Lake_compileStaticLib(x_1, x_2, x_3, x_7, x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MACOSX_DEPLOYMENT_TARGET", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("99.0", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
x_2 = l_Lake_compileLeanModule___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv() {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lake_compileO___closed__3;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
x_5 = lean_io_getenv(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
return x_6;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = l_Lake_compileO___closed__3;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
return x_2;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-shared", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileSharedLib___closed__0;
x_2 = l_Lake_compileSharedLib___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__16;
x_2 = l_Lake_compileSharedLib___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_1);
x_6 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_6);
lean_inc_ref(x_1);
x_7 = l_Lake_mkArgs(x_1, x_2, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
x_11 = l_Lake_compileLeanModule___closed__4;
x_12 = l_Lake_compileSharedLib___closed__3;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Array_append___redArg(x_13, x_8);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = 1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_17);
x_19 = l_Lake_proc(x_18, x_17, x_9);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_io_error_to_string(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_4);
x_29 = lean_array_push(x_4, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_compileSharedLib(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_1);
x_6 = l_Lake_createParentDirs(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_6);
lean_inc_ref(x_1);
x_7 = l_Lake_mkArgs(x_1, x_2, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv();
x_11 = l_Lake_compileLeanModule___closed__4;
x_12 = l_Lake_compileLeanModule___closed__17;
x_13 = lean_array_push(x_12, x_1);
x_14 = l_Array_append___redArg(x_13, x_8);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = 1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_17);
x_19 = l_Lake_proc(x_18, x_17, x_9);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec_ref(x_6);
x_25 = lean_io_error_to_string(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_4);
x_29 = lean_array_push(x_4, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_compileExe(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Array_append___redArg(x_4, x_8);
lean_dec_ref(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_download___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curl", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_download___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-s", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-S", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_download___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_download___closed__1;
x_2 = l_Lake_download___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_download___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_download___closed__2;
x_2 = l_Lake_download___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_download___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_download___closed__3;
x_2 = l_Lake_download___closed__7;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_download___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__16;
x_2 = l_Lake_download___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_18; lean_object* x_19; uint8_t x_36; 
x_36 = l_System_FilePath_pathExists(x_2);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc_ref(x_2);
x_37 = l_Lake_createParentDirs(x_2);
if (lean_obj_tag(x_37) == 0)
{
lean_dec_ref(x_37);
x_18 = x_4;
x_19 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_io_error_to_string(x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_4);
x_43 = lean_array_push(x_4, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; 
x_45 = lean_io_remove_file(x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_18 = x_4;
x_19 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_io_error_to_string(x_46);
x_48 = 3;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_array_get_size(x_4);
x_51 = lean_array_push(x_4, x_49);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
block_17:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lake_compileLeanModule___closed__4;
x_10 = l_Lake_download___closed__0;
x_11 = lean_box(0);
x_12 = l_Lake_compileO___closed__3;
x_13 = 1;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
x_16 = l_Lake_proc(x_15, x_13, x_6);
return x_16;
}
block_35:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = l_Lake_download___closed__4;
x_21 = l_Lake_download___closed__9;
x_22 = lean_array_push(x_21, x_2);
x_23 = lean_array_push(x_22, x_20);
x_24 = lean_array_push(x_23, x_1);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get_size(x_3);
x_27 = lean_nat_dec_lt(x_25, x_26);
if (x_27 == 0)
{
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_24;
goto block_17;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
if (x_27 == 0)
{
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_24;
goto block_17;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_26);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(x_3, x_29, x_30, x_24);
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_31;
goto block_17;
}
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_26);
x_34 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0(x_3, x_32, x_33, x_24);
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_34;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_download(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_untar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tar", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_untar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-C", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_untar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_untar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-xvv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_untar___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 122;
x_2 = l_Lake_untar___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_2);
x_6 = l_IO_FS_createDirAll(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_26; 
lean_dec_ref(x_6);
x_26 = l_Lake_untar___closed__3;
if (x_3 == 0)
{
x_7 = x_26;
x_8 = x_4;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = l_Lake_untar___closed__4;
x_7 = x_27;
x_8 = x_4;
goto block_25;
}
block_25:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_9 = l_Lake_compileLeanModule___closed__4;
x_10 = l_Lake_untar___closed__0;
x_11 = l_Lake_download___closed__3;
x_12 = l_Lake_untar___closed__1;
x_13 = l_Lake_untar___closed__2;
x_14 = lean_array_push(x_13, x_7);
x_15 = lean_array_push(x_14, x_11);
x_16 = lean_array_push(x_15, x_1);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_2);
x_19 = lean_box(0);
x_20 = l_Lake_compileO___closed__3;
x_21 = 1;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_22);
x_24 = l_Lake_proc(x_23, x_21, x_8);
return x_24;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec_ref(x_6);
x_29 = lean_io_error_to_string(x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_get_size(x_4);
x_33 = lean_array_push(x_4, x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_untar(x_1, x_2, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exclude=", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_9 = lean_array_uget(x_1, x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = lean_array_push(x_4, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lake_tar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_download___closed__3;
x_2 = l_Lake_untar___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_tar___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("COPYFILE_DISABLE", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_tar___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_tar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___closed__4;
x_2 = l_Lake_tar___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_tar___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___closed__5;
x_2 = l_Lake_compileLeanModule___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_tar___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-cvv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___closed__7;
x_2 = l_Lake_mkArgs___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_tar___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-z", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___closed__9;
x_2 = l_Lake_tar___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; 
lean_inc_ref(x_2);
x_19 = l_Lake_createParentDirs(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_47; 
lean_dec_ref(x_19);
x_47 = l_Lake_tar___closed__8;
if (x_3 == 0)
{
x_20 = x_47;
x_21 = x_5;
goto block_46;
}
else
{
lean_object* x_48; 
x_48 = l_Lake_tar___closed__10;
x_20 = x_48;
x_21 = x_5;
goto block_46;
}
block_46:
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_array_size(x_4);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0(x_4, x_22, x_23, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lake_compileLeanModule___closed__4;
x_28 = l_Lake_untar___closed__0;
x_29 = l_Lake_untar___closed__1;
x_30 = l_Lake_tar___closed__0;
x_31 = l_Lake_tar___closed__1;
x_32 = lean_array_push(x_31, x_2);
x_33 = lean_array_push(x_32, x_29);
x_34 = lean_array_push(x_33, x_1);
x_35 = lean_array_push(x_34, x_30);
x_36 = l_Array_append___redArg(x_25, x_35);
lean_dec_ref(x_35);
x_37 = lean_box(0);
x_38 = l_System_Platform_isOSX;
x_39 = 1;
if (x_38 == 0)
{
lean_object* x_40; 
x_40 = l_Lake_compileO___closed__3;
x_7 = x_39;
x_8 = x_28;
x_9 = lean_box(0);
x_10 = x_27;
x_11 = x_26;
x_12 = x_36;
x_13 = x_37;
x_14 = x_40;
goto block_18;
}
else
{
lean_object* x_41; 
x_41 = l_Lake_tar___closed__6;
x_7 = x_39;
x_8 = x_28;
x_9 = lean_box(0);
x_10 = x_27;
x_11 = x_26;
x_12 = x_36;
x_13 = x_37;
x_14 = x_41;
goto block_18;
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_ctor_get(x_19, 0);
lean_inc(x_49);
lean_dec_ref(x_19);
x_50 = lean_io_error_to_string(x_49);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_get_size(x_5);
x_54 = lean_array_push(x_5, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
block_18:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_7);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_15);
x_17 = l_Lake_proc(x_16, x_7, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lake_tar(x_1, x_2, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0 = _init_l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00Lake_compileLeanModule_spec__0___closed__0);
l_Lake_compileLeanModule___lam__0___closed__0 = _init_l_Lake_compileLeanModule___lam__0___closed__0();
lean_mark_persistent(l_Lake_compileLeanModule___lam__0___closed__0);
l_Lake_compileLeanModule___lam__0___closed__1 = _init_l_Lake_compileLeanModule___lam__0___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lam__0___closed__1);
l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00Lake_compileLeanModule_spec__1___redArg___closed__1);
l_Lake_compileLeanModule___closed__0 = _init_l_Lake_compileLeanModule___closed__0();
lean_mark_persistent(l_Lake_compileLeanModule___closed__0);
l_Lake_compileLeanModule___closed__1 = _init_l_Lake_compileLeanModule___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___closed__1);
l_Lake_compileLeanModule___closed__2 = _init_l_Lake_compileLeanModule___closed__2();
lean_mark_persistent(l_Lake_compileLeanModule___closed__2);
l_Lake_compileLeanModule___closed__3 = _init_l_Lake_compileLeanModule___closed__3();
lean_mark_persistent(l_Lake_compileLeanModule___closed__3);
l_Lake_compileLeanModule___closed__4 = _init_l_Lake_compileLeanModule___closed__4();
lean_mark_persistent(l_Lake_compileLeanModule___closed__4);
l_Lake_compileLeanModule___closed__5 = _init_l_Lake_compileLeanModule___closed__5();
lean_mark_persistent(l_Lake_compileLeanModule___closed__5);
l_Lake_compileLeanModule___closed__6 = _init_l_Lake_compileLeanModule___closed__6();
lean_mark_persistent(l_Lake_compileLeanModule___closed__6);
l_Lake_compileLeanModule___closed__7 = _init_l_Lake_compileLeanModule___closed__7();
lean_mark_persistent(l_Lake_compileLeanModule___closed__7);
l_Lake_compileLeanModule___closed__8 = _init_l_Lake_compileLeanModule___closed__8();
lean_mark_persistent(l_Lake_compileLeanModule___closed__8);
l_Lake_compileLeanModule___closed__9 = _init_l_Lake_compileLeanModule___closed__9();
lean_mark_persistent(l_Lake_compileLeanModule___closed__9);
l_Lake_compileLeanModule___closed__10 = _init_l_Lake_compileLeanModule___closed__10();
lean_mark_persistent(l_Lake_compileLeanModule___closed__10);
l_Lake_compileLeanModule___closed__11 = _init_l_Lake_compileLeanModule___closed__11();
lean_mark_persistent(l_Lake_compileLeanModule___closed__11);
l_Lake_compileLeanModule___closed__12 = _init_l_Lake_compileLeanModule___closed__12();
lean_mark_persistent(l_Lake_compileLeanModule___closed__12);
l_Lake_compileLeanModule___closed__13 = _init_l_Lake_compileLeanModule___closed__13();
lean_mark_persistent(l_Lake_compileLeanModule___closed__13);
l_Lake_compileLeanModule___closed__14 = _init_l_Lake_compileLeanModule___closed__14();
lean_mark_persistent(l_Lake_compileLeanModule___closed__14);
l_Lake_compileLeanModule___closed__15 = _init_l_Lake_compileLeanModule___closed__15();
lean_mark_persistent(l_Lake_compileLeanModule___closed__15);
l_Lake_compileLeanModule___closed__16 = _init_l_Lake_compileLeanModule___closed__16();
lean_mark_persistent(l_Lake_compileLeanModule___closed__16);
l_Lake_compileLeanModule___closed__17 = _init_l_Lake_compileLeanModule___closed__17();
lean_mark_persistent(l_Lake_compileLeanModule___closed__17);
l_Lake_compileO___closed__0 = _init_l_Lake_compileO___closed__0();
lean_mark_persistent(l_Lake_compileO___closed__0);
l_Lake_compileO___closed__1 = _init_l_Lake_compileO___closed__1();
lean_mark_persistent(l_Lake_compileO___closed__1);
l_Lake_compileO___closed__2 = _init_l_Lake_compileO___closed__2();
lean_mark_persistent(l_Lake_compileO___closed__2);
l_Lake_compileO___closed__3 = _init_l_Lake_compileO___closed__3();
lean_mark_persistent(l_Lake_compileO___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_mkArgs_spec__1___closed__1);
l_Lake_mkArgs___closed__0 = _init_l_Lake_mkArgs___closed__0();
lean_mark_persistent(l_Lake_mkArgs___closed__0);
l_Lake_mkArgs___closed__1 = _init_l_Lake_mkArgs___closed__1();
lean_mark_persistent(l_Lake_mkArgs___closed__1);
l_Lake_mkArgs___closed__2 = _init_l_Lake_mkArgs___closed__2();
lean_mark_persistent(l_Lake_mkArgs___closed__2);
l_Lake_compileStaticLib___closed__0 = _init_l_Lake_compileStaticLib___closed__0();
lean_mark_persistent(l_Lake_compileStaticLib___closed__0);
l_Lake_compileStaticLib___closed__1 = _init_l_Lake_compileStaticLib___closed__1();
lean_mark_persistent(l_Lake_compileStaticLib___closed__1);
l_Lake_compileStaticLib___closed__2 = _init_l_Lake_compileStaticLib___closed__2();
lean_mark_persistent(l_Lake_compileStaticLib___closed__2);
l_Lake_compileStaticLib___closed__3 = _init_l_Lake_compileStaticLib___closed__3();
lean_mark_persistent(l_Lake_compileStaticLib___closed__3);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4);
l_Lake_compileSharedLib___closed__0 = _init_l_Lake_compileSharedLib___closed__0();
lean_mark_persistent(l_Lake_compileSharedLib___closed__0);
l_Lake_compileSharedLib___closed__1 = _init_l_Lake_compileSharedLib___closed__1();
lean_mark_persistent(l_Lake_compileSharedLib___closed__1);
l_Lake_compileSharedLib___closed__2 = _init_l_Lake_compileSharedLib___closed__2();
lean_mark_persistent(l_Lake_compileSharedLib___closed__2);
l_Lake_compileSharedLib___closed__3 = _init_l_Lake_compileSharedLib___closed__3();
lean_mark_persistent(l_Lake_compileSharedLib___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_download_spec__0___closed__1);
l_Lake_download___closed__0 = _init_l_Lake_download___closed__0();
lean_mark_persistent(l_Lake_download___closed__0);
l_Lake_download___closed__1 = _init_l_Lake_download___closed__1();
lean_mark_persistent(l_Lake_download___closed__1);
l_Lake_download___closed__2 = _init_l_Lake_download___closed__2();
lean_mark_persistent(l_Lake_download___closed__2);
l_Lake_download___closed__3 = _init_l_Lake_download___closed__3();
lean_mark_persistent(l_Lake_download___closed__3);
l_Lake_download___closed__4 = _init_l_Lake_download___closed__4();
lean_mark_persistent(l_Lake_download___closed__4);
l_Lake_download___closed__5 = _init_l_Lake_download___closed__5();
lean_mark_persistent(l_Lake_download___closed__5);
l_Lake_download___closed__6 = _init_l_Lake_download___closed__6();
lean_mark_persistent(l_Lake_download___closed__6);
l_Lake_download___closed__7 = _init_l_Lake_download___closed__7();
lean_mark_persistent(l_Lake_download___closed__7);
l_Lake_download___closed__8 = _init_l_Lake_download___closed__8();
lean_mark_persistent(l_Lake_download___closed__8);
l_Lake_download___closed__9 = _init_l_Lake_download___closed__9();
lean_mark_persistent(l_Lake_download___closed__9);
l_Lake_untar___closed__0 = _init_l_Lake_untar___closed__0();
lean_mark_persistent(l_Lake_untar___closed__0);
l_Lake_untar___closed__1 = _init_l_Lake_untar___closed__1();
lean_mark_persistent(l_Lake_untar___closed__1);
l_Lake_untar___closed__2 = _init_l_Lake_untar___closed__2();
lean_mark_persistent(l_Lake_untar___closed__2);
l_Lake_untar___closed__3 = _init_l_Lake_untar___closed__3();
lean_mark_persistent(l_Lake_untar___closed__3);
l_Lake_untar___closed__4 = _init_l_Lake_untar___closed__4();
lean_mark_persistent(l_Lake_untar___closed__4);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_tar_spec__0___closed__0);
l_Lake_tar___closed__0 = _init_l_Lake_tar___closed__0();
lean_mark_persistent(l_Lake_tar___closed__0);
l_Lake_tar___closed__1 = _init_l_Lake_tar___closed__1();
lean_mark_persistent(l_Lake_tar___closed__1);
l_Lake_tar___closed__2 = _init_l_Lake_tar___closed__2();
lean_mark_persistent(l_Lake_tar___closed__2);
l_Lake_tar___closed__3 = _init_l_Lake_tar___closed__3();
lean_mark_persistent(l_Lake_tar___closed__3);
l_Lake_tar___closed__4 = _init_l_Lake_tar___closed__4();
lean_mark_persistent(l_Lake_tar___closed__4);
l_Lake_tar___closed__5 = _init_l_Lake_tar___closed__5();
lean_mark_persistent(l_Lake_tar___closed__5);
l_Lake_tar___closed__6 = _init_l_Lake_tar___closed__6();
lean_mark_persistent(l_Lake_tar___closed__6);
l_Lake_tar___closed__7 = _init_l_Lake_tar___closed__7();
lean_mark_persistent(l_Lake_tar___closed__7);
l_Lake_tar___closed__8 = _init_l_Lake_tar___closed__8();
lean_mark_persistent(l_Lake_tar___closed__8);
l_Lake_tar___closed__9 = _init_l_Lake_tar___closed__9();
lean_mark_persistent(l_Lake_tar___closed__9);
l_Lake_tar___closed__10 = _init_l_Lake_tar___closed__10();
lean_mark_persistent(l_Lake_tar___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
