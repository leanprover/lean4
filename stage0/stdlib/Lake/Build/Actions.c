// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lean.Setup public import Lake.Util.Log import Lean.Data.Json import Lake.Config.Dynlib import Lake.Util.Proc import Lake.Util.NativeLib import Lake.Util.FilePath import Lake.Util.IO
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
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__8;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__9;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__5;
static lean_object* l_Lake_compileLeanModule___closed__6;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__13;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__10;
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lake_compileLeanModule___closed__5;
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__17;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_compileLeanModule_spec__2(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__11;
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__4;
static lean_object* l_Lake_download___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__7;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__0;
lean_object* l_Lake_removeFileIfExists(lean_object*, lean_object*);
static uint8_t l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
static lean_object* l_Lake_tar___closed__8;
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__9;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___Lake_compileLeanModule_spec__2___boxed(lean_object*);
static lean_object* l_Lake_mkArgs___closed__3;
static lean_object* l_Lake_compileLeanModule___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__0;
lean_object* l_IO_Process_output(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__3;
static lean_object* l_Lake_compileSharedLib___closed__0;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__15;
static lean_object* l_Lake_download___closed__4;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__16;
static lean_object* l_Lake_untar___closed__2;
static uint8_t l_Lake_mkArgs___closed__0;
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0;
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_compileO___closed__0;
static lean_object* l_Lake_untar___closed__4;
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
lean_object* l_Lean_instFromJsonSerialMessage_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__1;
static lean_object* l_Lake_compileSharedLib___closed__3;
static lean_object* l_Lake_compileStaticLib___closed__0;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__5;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__6;
static lean_object* l_Lake_compileO___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__14;
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__7;
static lean_object* l_Lake_compileLeanModule___closed__4;
static lean_object* l_Lake_compileLeanModule___closed__12;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_compileO___closed__2;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l_Lake_compileLeanModule___closed__3;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_mkArgs___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__8;
static lean_object* l_Lake_mkArgs___closed__1;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__3;
static lean_object* l_Lake_download___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__2;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
static lean_object* l_Lake_download___closed__2;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__10;
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_tar___closed__7;
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__1;
static lean_object* l_Lake_compileO___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__3;
static lean_object* l_Lake_tar___closed__9;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 10;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___redArg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_compileLeanModule_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2(x_1, x_2, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_22; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
lean_inc(x_8);
x_22 = l_Lean_Json_parse(x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_instFromJsonSerialMessage_fromJson(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
goto block_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_65 = lean_string_utf8_byte_size(x_2);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_68 = l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1;
x_69 = lean_string_append(x_68, x_2);
x_70 = 1;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_push(x_4, x_71);
x_26 = x_72;
x_27 = x_5;
goto block_64;
}
else
{
x_26 = x_4;
x_27 = x_5;
goto block_64;
}
block_64:
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*5 + 2);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_dec(x_33);
lean_inc_ref(x_1);
x_34 = l_Lake_mkRelPathString(x_1);
lean_ctor_set(x_28, 0, x_34);
x_35 = l_Lake_LogEntry_ofSerialMessage(x_25);
x_36 = lean_array_push(x_26, x_35);
x_3 = x_9;
x_4 = x_36;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_28, 1);
x_39 = lean_ctor_get(x_28, 2);
x_40 = lean_ctor_get_uint8(x_28, sizeof(void*)*5);
x_41 = lean_ctor_get_uint8(x_28, sizeof(void*)*5 + 1);
x_42 = lean_ctor_get(x_28, 3);
x_43 = lean_ctor_get(x_28, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
lean_inc_ref(x_1);
x_44 = l_Lake_mkRelPathString(x_1);
x_45 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
lean_ctor_set(x_45, 2, x_39);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*5, x_40);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 1, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*5 + 2, x_29);
lean_ctor_set(x_25, 0, x_45);
x_46 = l_Lake_LogEntry_ofSerialMessage(x_25);
x_47 = lean_array_push(x_26, x_46);
x_3 = x_9;
x_4 = x_47;
x_5 = x_27;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_dec(x_25);
x_50 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_28, 2);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_28, sizeof(void*)*5);
x_53 = lean_ctor_get_uint8(x_28, sizeof(void*)*5 + 1);
x_54 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_28, 4);
lean_inc(x_55);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 x_56 = x_28;
} else {
 lean_dec_ref(x_28);
 x_56 = lean_box(0);
}
lean_inc_ref(x_1);
x_57 = l_Lake_mkRelPathString(x_1);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 5, 3);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 1, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 2, x_29);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
x_60 = l_Lake_LogEntry_ofSerialMessage(x_59);
x_61 = lean_array_push(x_26, x_60);
x_3 = x_9;
x_4 = x_61;
x_5 = x_27;
goto _start;
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_25);
x_3 = x_9;
x_4 = x_26;
x_5 = x_27;
goto _start;
}
}
}
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_string_append(x_2, x_8);
lean_dec(x_8);
x_11 = l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_2 = x_12;
x_3 = x_9;
goto _start;
}
block_21:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_byte_size(x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
goto block_14;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_string_utf8_byte_size(x_8);
x_19 = lean_nat_dec_eq(x_18, x_16);
lean_dec(x_18);
if (x_19 == 0)
{
goto block_14;
}
else
{
lean_dec(x_8);
x_3 = x_9;
goto _start;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_string_utf8_byte_size(x_2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_28 = l_Lake_compileLeanModule___lam__0___closed__1;
x_29 = l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0(x_2, x_25, x_26);
x_30 = l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1(x_2, x_29, x_25);
x_31 = lean_string_utf8_extract(x_2, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = lean_string_append(x_28, x_31);
lean_dec_ref(x_31);
x_33 = 1;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_push(x_4, x_34);
x_6 = x_35;
x_7 = x_5;
goto block_24;
}
else
{
lean_dec(x_25);
x_6 = x_4;
x_7 = x_5;
goto block_24;
}
block_24:
{
uint32_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_uint32_dec_eq(x_1, x_8);
x_10 = l_instDecidableNot___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = l_Lake_compileLeanModule___lam__0___closed__0;
x_15 = lean_uint32_to_nat(x_1);
x_16 = l_Nat_reprFast(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec_ref(x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_6);
x_21 = lean_array_push(x_6, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
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
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_360; 
x_272 = lean_ctor_get(x_5, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_5, 4);
lean_inc(x_273);
x_274 = lean_ctor_get(x_5, 6);
lean_inc(x_274);
x_275 = lean_ctor_get(x_5, 7);
lean_inc(x_275);
lean_dec_ref(x_5);
x_360 = lean_array_push(x_6, x_1);
if (lean_obj_tag(x_272) == 0)
{
x_332 = x_360;
x_333 = x_9;
x_334 = x_10;
goto block_359;
}
else
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_272, 0);
lean_inc(x_361);
lean_dec_ref(x_272);
x_362 = l_Lake_createParentDirs(x_361, x_10);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l_Lake_compileLeanModule___closed__17;
x_365 = lean_array_push(x_364, x_361);
x_366 = l_Array_append___redArg(x_360, x_365);
lean_dec_ref(x_365);
x_332 = x_366;
x_333 = x_9;
x_334 = x_363;
goto block_359;
}
else
{
uint8_t x_367; 
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_367 = !lean_is_exclusive(x_362);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_368 = lean_ctor_get(x_362, 0);
x_369 = lean_ctor_get(x_362, 1);
x_370 = lean_io_error_to_string(x_368);
x_371 = 3;
x_372 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*1, x_371);
x_373 = lean_array_get_size(x_9);
x_374 = lean_array_push(x_9, x_372);
lean_ctor_set(x_362, 1, x_374);
lean_ctor_set(x_362, 0, x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_362);
lean_ctor_set(x_375, 1, x_369);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_376 = lean_ctor_get(x_362, 0);
x_377 = lean_ctor_get(x_362, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_362);
x_378 = lean_io_error_to_string(x_376);
x_379 = 3;
x_380 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_379);
x_381 = lean_array_get_size(x_9);
x_382 = lean_array_push(x_9, x_380);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_377);
return x_384;
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
block_22:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_11 = x_17;
x_12 = x_21;
x_13 = x_20;
goto block_16;
}
}
block_271:
{
lean_object* x_26; 
x_26 = l_Lake_createParentDirs(x_4, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 1);
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_Lean_instToJsonModuleSetup_toJson(x_3);
x_31 = lean_unsigned_to_nat(80u);
x_32 = l_Lean_Json_pretty(x_30, x_31);
x_33 = l_IO_FS_writeFile(x_4, x_32, x_28);
lean_dec_ref(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_free_object(x_26);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = l_Lake_compileLeanModule___closed__2;
x_38 = lean_array_push(x_37, x_4);
x_39 = l_Array_append___redArg(x_23, x_38);
lean_dec_ref(x_38);
x_40 = l_Lake_compileLeanModule___closed__3;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lake_compileLeanModule___closed__4;
x_43 = lean_box(0);
x_44 = l_Lake_compileLeanModule___closed__5;
x_45 = l_System_SearchPath_toString(x_7);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_33, 1, x_46);
lean_ctor_set(x_33, 0, x_44);
x_47 = l_Lake_compileLeanModule___closed__6;
x_48 = lean_array_push(x_47, x_33);
x_49 = 1;
x_50 = 0;
lean_inc_ref(x_8);
x_51 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_8);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_43);
lean_ctor_set(x_51, 4, x_48);
lean_ctor_set_uint8(x_51, sizeof(void*)*5, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*5 + 1, x_50);
x_52 = lean_array_get_size(x_24);
lean_inc_ref(x_51);
x_53 = l_Lake_mkCmdLog(x_51);
x_54 = 0;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
x_56 = lean_array_push(x_24, x_55);
x_57 = l_IO_Process_output(x_51, x_43, x_35);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint32_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec_ref(x_8);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_ctor_get_uint32(x_58, sizeof(void*)*2);
x_61 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_62);
lean_dec(x_58);
x_63 = lean_string_utf8_byte_size(x_61);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_nat_dec_eq(x_63, x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = l_Lake_compileLeanModule___closed__7;
x_67 = l_String_split___at___Lake_compileLeanModule_spec__2(x_61);
lean_dec_ref(x_61);
x_68 = l_List_foldlM___at___Lake_compileLeanModule_spec__4(x_2, x_66, x_67, x_56, x_59);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_string_utf8_byte_size(x_71);
x_74 = lean_nat_dec_eq(x_73, x_64);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1;
x_76 = lean_string_append(x_75, x_71);
lean_dec(x_71);
x_77 = 1;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_box(0);
x_80 = lean_array_push(x_72, x_78);
x_81 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_79, x_80, x_70);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_81;
goto block_22;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_71);
x_82 = lean_box(0);
x_83 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_82, x_72, x_70);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_83;
goto block_22;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec_ref(x_61);
lean_dec_ref(x_2);
x_84 = lean_box(0);
x_85 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_84, x_56, x_59);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_85;
goto block_22;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_2);
x_86 = lean_ctor_get(x_57, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_57, 1);
lean_inc(x_87);
lean_dec_ref(x_57);
x_88 = l_Lake_compileLeanModule___closed__8;
x_89 = lean_string_append(x_88, x_8);
lean_dec_ref(x_8);
x_90 = l_Lake_compileLeanModule___closed__9;
x_91 = lean_string_append(x_89, x_90);
x_92 = lean_io_error_to_string(x_86);
x_93 = lean_string_append(x_91, x_92);
lean_dec_ref(x_92);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_array_push(x_56, x_95);
x_11 = x_52;
x_12 = x_96;
x_13 = x_87;
goto block_16;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_97 = lean_ctor_get(x_33, 1);
lean_inc(x_97);
lean_dec(x_33);
x_98 = l_Lake_compileLeanModule___closed__2;
x_99 = lean_array_push(x_98, x_4);
x_100 = l_Array_append___redArg(x_23, x_99);
lean_dec_ref(x_99);
x_101 = l_Lake_compileLeanModule___closed__3;
x_102 = lean_array_push(x_100, x_101);
x_103 = l_Lake_compileLeanModule___closed__4;
x_104 = lean_box(0);
x_105 = l_Lake_compileLeanModule___closed__5;
x_106 = l_System_SearchPath_toString(x_7);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lake_compileLeanModule___closed__6;
x_110 = lean_array_push(x_109, x_108);
x_111 = 1;
x_112 = 0;
lean_inc_ref(x_8);
x_113 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_8);
lean_ctor_set(x_113, 2, x_102);
lean_ctor_set(x_113, 3, x_104);
lean_ctor_set(x_113, 4, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*5, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*5 + 1, x_112);
x_114 = lean_array_get_size(x_24);
lean_inc_ref(x_113);
x_115 = l_Lake_mkCmdLog(x_113);
x_116 = 0;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_push(x_24, x_117);
x_119 = l_IO_Process_output(x_113, x_104, x_97);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint32_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
lean_dec_ref(x_8);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get_uint32(x_120, sizeof(void*)*2);
x_123 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc_ref(x_124);
lean_dec(x_120);
x_125 = lean_string_utf8_byte_size(x_123);
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_128 = l_Lake_compileLeanModule___closed__7;
x_129 = l_String_split___at___Lake_compileLeanModule_spec__2(x_123);
lean_dec_ref(x_123);
x_130 = l_List_foldlM___at___Lake_compileLeanModule_spec__4(x_2, x_128, x_129, x_118, x_121);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec_ref(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_string_utf8_byte_size(x_133);
x_136 = lean_nat_dec_eq(x_135, x_126);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1;
x_138 = lean_string_append(x_137, x_133);
lean_dec(x_133);
x_139 = 1;
x_140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set_uint8(x_140, sizeof(void*)*1, x_139);
x_141 = lean_box(0);
x_142 = lean_array_push(x_134, x_140);
x_143 = l_Lake_compileLeanModule___lam__0(x_122, x_124, x_141, x_142, x_132);
lean_dec_ref(x_124);
x_17 = x_114;
x_18 = x_143;
goto block_22;
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_133);
x_144 = lean_box(0);
x_145 = l_Lake_compileLeanModule___lam__0(x_122, x_124, x_144, x_134, x_132);
lean_dec_ref(x_124);
x_17 = x_114;
x_18 = x_145;
goto block_22;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_123);
lean_dec_ref(x_2);
x_146 = lean_box(0);
x_147 = l_Lake_compileLeanModule___lam__0(x_122, x_124, x_146, x_118, x_121);
lean_dec_ref(x_124);
x_17 = x_114;
x_18 = x_147;
goto block_22;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_119, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_119, 1);
lean_inc(x_149);
lean_dec_ref(x_119);
x_150 = l_Lake_compileLeanModule___closed__8;
x_151 = lean_string_append(x_150, x_8);
lean_dec_ref(x_8);
x_152 = l_Lake_compileLeanModule___closed__9;
x_153 = lean_string_append(x_151, x_152);
x_154 = lean_io_error_to_string(x_148);
x_155 = lean_string_append(x_153, x_154);
lean_dec_ref(x_154);
x_156 = 3;
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
x_158 = lean_array_push(x_118, x_157);
x_11 = x_114;
x_12 = x_158;
x_13 = x_149;
goto block_16;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_159 = !lean_is_exclusive(x_33);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_33, 0);
x_161 = lean_ctor_get(x_33, 1);
x_162 = lean_io_error_to_string(x_160);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_get_size(x_24);
x_166 = lean_array_push(x_24, x_164);
lean_ctor_set(x_33, 1, x_166);
lean_ctor_set(x_33, 0, x_165);
lean_ctor_set(x_26, 1, x_161);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_33, 0);
x_168 = lean_ctor_get(x_33, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_33);
x_169 = lean_io_error_to_string(x_167);
x_170 = 3;
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_170);
x_172 = lean_array_get_size(x_24);
x_173 = lean_array_push(x_24, x_171);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set(x_26, 1, x_168);
lean_ctor_set(x_26, 0, x_174);
return x_26;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_26, 1);
lean_inc(x_175);
lean_dec(x_26);
x_176 = l_Lean_instToJsonModuleSetup_toJson(x_3);
x_177 = lean_unsigned_to_nat(80u);
x_178 = l_Lean_Json_pretty(x_176, x_177);
x_179 = l_IO_FS_writeFile(x_4, x_178, x_175);
lean_dec_ref(x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = l_Lake_compileLeanModule___closed__2;
x_183 = lean_array_push(x_182, x_4);
x_184 = l_Array_append___redArg(x_23, x_183);
lean_dec_ref(x_183);
x_185 = l_Lake_compileLeanModule___closed__3;
x_186 = lean_array_push(x_184, x_185);
x_187 = l_Lake_compileLeanModule___closed__4;
x_188 = lean_box(0);
x_189 = l_Lake_compileLeanModule___closed__5;
x_190 = l_System_SearchPath_toString(x_7);
x_191 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lake_compileLeanModule___closed__6;
x_194 = lean_array_push(x_193, x_192);
x_195 = 1;
x_196 = 0;
lean_inc_ref(x_8);
x_197 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_197, 0, x_187);
lean_ctor_set(x_197, 1, x_8);
lean_ctor_set(x_197, 2, x_186);
lean_ctor_set(x_197, 3, x_188);
lean_ctor_set(x_197, 4, x_194);
lean_ctor_set_uint8(x_197, sizeof(void*)*5, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*5 + 1, x_196);
x_198 = lean_array_get_size(x_24);
lean_inc_ref(x_197);
x_199 = l_Lake_mkCmdLog(x_197);
x_200 = 0;
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_200);
x_202 = lean_array_push(x_24, x_201);
x_203 = l_IO_Process_output(x_197, x_188, x_180);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; uint32_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec_ref(x_8);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = lean_ctor_get_uint32(x_204, sizeof(void*)*2);
x_207 = lean_ctor_get(x_204, 0);
lean_inc_ref(x_207);
x_208 = lean_ctor_get(x_204, 1);
lean_inc_ref(x_208);
lean_dec(x_204);
x_209 = lean_string_utf8_byte_size(x_207);
x_210 = lean_unsigned_to_nat(0u);
x_211 = lean_nat_dec_eq(x_209, x_210);
lean_dec(x_209);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_212 = l_Lake_compileLeanModule___closed__7;
x_213 = l_String_split___at___Lake_compileLeanModule_spec__2(x_207);
lean_dec_ref(x_207);
x_214 = l_List_foldlM___at___Lake_compileLeanModule_spec__4(x_2, x_212, x_213, x_202, x_205);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_string_utf8_byte_size(x_217);
x_220 = lean_nat_dec_eq(x_219, x_210);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_221 = l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1;
x_222 = lean_string_append(x_221, x_217);
lean_dec(x_217);
x_223 = 1;
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_223);
x_225 = lean_box(0);
x_226 = lean_array_push(x_218, x_224);
x_227 = l_Lake_compileLeanModule___lam__0(x_206, x_208, x_225, x_226, x_216);
lean_dec_ref(x_208);
x_17 = x_198;
x_18 = x_227;
goto block_22;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_217);
x_228 = lean_box(0);
x_229 = l_Lake_compileLeanModule___lam__0(x_206, x_208, x_228, x_218, x_216);
lean_dec_ref(x_208);
x_17 = x_198;
x_18 = x_229;
goto block_22;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec_ref(x_207);
lean_dec_ref(x_2);
x_230 = lean_box(0);
x_231 = l_Lake_compileLeanModule___lam__0(x_206, x_208, x_230, x_202, x_205);
lean_dec_ref(x_208);
x_17 = x_198;
x_18 = x_231;
goto block_22;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; 
lean_dec_ref(x_2);
x_232 = lean_ctor_get(x_203, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_203, 1);
lean_inc(x_233);
lean_dec_ref(x_203);
x_234 = l_Lake_compileLeanModule___closed__8;
x_235 = lean_string_append(x_234, x_8);
lean_dec_ref(x_8);
x_236 = l_Lake_compileLeanModule___closed__9;
x_237 = lean_string_append(x_235, x_236);
x_238 = lean_io_error_to_string(x_232);
x_239 = lean_string_append(x_237, x_238);
lean_dec_ref(x_238);
x_240 = 3;
x_241 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set_uint8(x_241, sizeof(void*)*1, x_240);
x_242 = lean_array_push(x_202, x_241);
x_11 = x_198;
x_12 = x_242;
x_13 = x_233;
goto block_16;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_243 = lean_ctor_get(x_179, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_179, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_245 = x_179;
} else {
 lean_dec_ref(x_179);
 x_245 = lean_box(0);
}
x_246 = lean_io_error_to_string(x_243);
x_247 = 3;
x_248 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_247);
x_249 = lean_array_get_size(x_24);
x_250 = lean_array_push(x_24, x_248);
if (lean_is_scalar(x_245)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_245;
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_244);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_253 = !lean_is_exclusive(x_26);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_254 = lean_ctor_get(x_26, 0);
x_255 = lean_ctor_get(x_26, 1);
x_256 = lean_io_error_to_string(x_254);
x_257 = 3;
x_258 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set_uint8(x_258, sizeof(void*)*1, x_257);
x_259 = lean_array_get_size(x_24);
x_260 = lean_array_push(x_24, x_258);
lean_ctor_set(x_26, 1, x_260);
lean_ctor_set(x_26, 0, x_259);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_26);
lean_ctor_set(x_261, 1, x_255);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_262 = lean_ctor_get(x_26, 0);
x_263 = lean_ctor_get(x_26, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_26);
x_264 = lean_io_error_to_string(x_262);
x_265 = 3;
x_266 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set_uint8(x_266, sizeof(void*)*1, x_265);
x_267 = lean_array_get_size(x_24);
x_268 = lean_array_push(x_24, x_266);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_263);
return x_270;
}
}
}
block_303:
{
if (lean_obj_tag(x_275) == 0)
{
x_23 = x_276;
x_24 = x_277;
x_25 = x_278;
goto block_271;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_275, 0);
lean_inc(x_279);
lean_dec_ref(x_275);
x_280 = l_Lake_createParentDirs(x_279, x_278);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec_ref(x_280);
x_282 = l_Lake_compileLeanModule___closed__11;
x_283 = lean_array_push(x_282, x_279);
x_284 = l_Array_append___redArg(x_276, x_283);
lean_dec_ref(x_283);
x_23 = x_284;
x_24 = x_277;
x_25 = x_281;
goto block_271;
}
else
{
uint8_t x_285; 
lean_dec(x_279);
lean_dec_ref(x_276);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_285 = !lean_is_exclusive(x_280);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_286 = lean_ctor_get(x_280, 0);
x_287 = lean_ctor_get(x_280, 1);
x_288 = lean_io_error_to_string(x_286);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = lean_array_get_size(x_277);
x_292 = lean_array_push(x_277, x_290);
lean_ctor_set(x_280, 1, x_292);
lean_ctor_set(x_280, 0, x_291);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_280);
lean_ctor_set(x_293, 1, x_287);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_294 = lean_ctor_get(x_280, 0);
x_295 = lean_ctor_get(x_280, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_280);
x_296 = lean_io_error_to_string(x_294);
x_297 = 3;
x_298 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_297);
x_299 = lean_array_get_size(x_277);
x_300 = lean_array_push(x_277, x_298);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_295);
return x_302;
}
}
}
}
block_331:
{
if (lean_obj_tag(x_274) == 0)
{
x_276 = x_304;
x_277 = x_305;
x_278 = x_306;
goto block_303;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_274, 0);
lean_inc(x_307);
lean_dec_ref(x_274);
x_308 = l_Lake_createParentDirs(x_307, x_306);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = l_Lake_compileLeanModule___closed__13;
x_311 = lean_array_push(x_310, x_307);
x_312 = l_Array_append___redArg(x_304, x_311);
lean_dec_ref(x_311);
x_276 = x_312;
x_277 = x_305;
x_278 = x_309;
goto block_303;
}
else
{
uint8_t x_313; 
lean_dec(x_307);
lean_dec_ref(x_304);
lean_dec(x_275);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_313 = !lean_is_exclusive(x_308);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_314 = lean_ctor_get(x_308, 0);
x_315 = lean_ctor_get(x_308, 1);
x_316 = lean_io_error_to_string(x_314);
x_317 = 3;
x_318 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set_uint8(x_318, sizeof(void*)*1, x_317);
x_319 = lean_array_get_size(x_305);
x_320 = lean_array_push(x_305, x_318);
lean_ctor_set(x_308, 1, x_320);
lean_ctor_set(x_308, 0, x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_308);
lean_ctor_set(x_321, 1, x_315);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_322 = lean_ctor_get(x_308, 0);
x_323 = lean_ctor_get(x_308, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_308);
x_324 = lean_io_error_to_string(x_322);
x_325 = 3;
x_326 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_325);
x_327 = lean_array_get_size(x_305);
x_328 = lean_array_push(x_305, x_326);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_323);
return x_330;
}
}
}
}
block_359:
{
if (lean_obj_tag(x_273) == 0)
{
x_304 = x_332;
x_305 = x_333;
x_306 = x_334;
goto block_331;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_273, 0);
lean_inc(x_335);
lean_dec_ref(x_273);
x_336 = l_Lake_createParentDirs(x_335, x_334);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec_ref(x_336);
x_338 = l_Lake_compileLeanModule___closed__15;
x_339 = lean_array_push(x_338, x_335);
x_340 = l_Array_append___redArg(x_332, x_339);
lean_dec_ref(x_339);
x_304 = x_340;
x_305 = x_333;
x_306 = x_337;
goto block_331;
}
else
{
uint8_t x_341; 
lean_dec(x_335);
lean_dec_ref(x_332);
lean_dec(x_275);
lean_dec(x_274);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_341 = !lean_is_exclusive(x_336);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_342 = lean_ctor_get(x_336, 0);
x_343 = lean_ctor_get(x_336, 1);
x_344 = lean_io_error_to_string(x_342);
x_345 = 3;
x_346 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set_uint8(x_346, sizeof(void*)*1, x_345);
x_347 = lean_array_get_size(x_333);
x_348 = lean_array_push(x_333, x_346);
lean_ctor_set(x_336, 1, x_348);
lean_ctor_set(x_336, 0, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_336);
lean_ctor_set(x_349, 1, x_343);
return x_349;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_350 = lean_ctor_get(x_336, 0);
x_351 = lean_ctor_get(x_336, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_336);
x_352 = lean_io_error_to_string(x_350);
x_353 = 3;
x_354 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_353);
x_355 = lean_array_get_size(x_333);
x_356 = lean_array_push(x_333, x_354);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_351);
return x_358;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lake_compileLeanModule_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_compileLeanModule_spec__2_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_compileLeanModule_spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_compileLeanModule_spec__2(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_7 = l_Lake_compileLeanModule___lam__0(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_createParentDirs(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lake_compileLeanModule___closed__4;
x_10 = l_Lake_compileO___closed__2;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_2);
x_13 = l_Array_append___redArg(x_12, x_3);
x_14 = lean_box(0);
x_15 = l_Lake_compileO___closed__3;
x_16 = 1;
x_17 = 0;
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_17);
x_19 = l_Lake_proc(x_18, x_17, x_5, x_8);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_io_error_to_string(x_21);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_5);
x_27 = lean_array_push(x_5, x_25);
lean_ctor_set(x_7, 1, x_27);
lean_ctor_set(x_7, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_7, 0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_7);
x_31 = lean_io_error_to_string(x_29);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_5);
x_35 = lean_array_push(x_5, x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_13; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = 92;
x_13 = lean_uint32_dec_eq(x_7, x_8);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 34;
x_15 = lean_uint32_dec_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_string_push(x_4, x_7);
x_3 = x_6;
x_4 = x_16;
goto _start;
}
else
{
goto block_12;
}
}
else
{
goto block_12;
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_string_push(x_4, x_8);
x_10 = lean_string_push(x_9, x_7);
x_3 = x_6;
x_4 = x_10;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_array_uget(x_2, x_3);
x_10 = l_Lake_compileLeanModule___closed__7;
x_11 = lean_string_utf8_byte_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_String_foldlAux___at___Lake_mkArgs_spec__0(x_9, x_11, x_12, x_10);
lean_dec(x_11);
lean_dec_ref(x_9);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0;
x_15 = lean_string_append(x_14, x_13);
lean_dec_ref(x_13);
x_16 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_io_prim_handle_put_str(x_1, x_17, x_7);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_19;
x_7 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
x_27 = lean_io_error_to_string(x_25);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_6);
x_31 = lean_array_push(x_6, x_29);
lean_ctor_set(x_18, 1, x_31);
lean_ctor_set(x_18, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_io_error_to_string(x_33);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_6);
x_39 = lean_array_push(x_6, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_6);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_7);
return x_43;
}
}
}
static uint8_t _init_l_Lake_mkArgs___closed__0() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
return x_1;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rsp", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_mkArgs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lake_mkArgs___closed__0;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_19; lean_object* x_20; 
x_8 = l_Lake_mkArgs___closed__1;
x_9 = l_System_FilePath_addExtension(x_1, x_8);
x_19 = 1;
x_20 = lean_io_prim_handle_mk(x_9, x_19, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_2);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_2);
x_10 = x_3;
x_11 = x_22;
goto block_18;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec_ref(x_2);
x_10 = x_3;
x_11 = x_22;
goto block_18;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_box(0);
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(x_21, x_2, x_28, x_29, x_27, x_3, x_22);
lean_dec_ref(x_2);
lean_dec(x_21);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_10 = x_33;
x_11 = x_32;
goto block_18;
}
else
{
uint8_t x_34; 
lean_dec_ref(x_9);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_31, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_43 = x_31;
} else {
 lean_dec_ref(x_31);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
x_49 = lean_io_error_to_string(x_47);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_get_size(x_3);
x_53 = lean_array_push(x_3, x_51);
lean_ctor_set(x_20, 1, x_53);
lean_ctor_set(x_20, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_20);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_io_error_to_string(x_55);
x_58 = 3;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_get_size(x_3);
x_61 = lean_array_push(x_3, x_59);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lake_mkArgs___closed__2;
x_13 = lean_string_append(x_12, x_9);
lean_dec_ref(x_9);
x_14 = l_Lake_mkArgs___closed__3;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___Lake_mkArgs_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_2 = l_Lake_mkArgs___closed__3;
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
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_createParentDirs(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_Lake_removeFileIfExists(x_1, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_free_object(x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lake_compileStaticLib___closed__1;
x_14 = 1;
if (x_4 == 0)
{
x_15 = x_13;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = l_Lake_compileStaticLib___closed__3;
x_15 = x_45;
goto block_44;
}
block_44:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_array_size(x_2);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(x_16, x_17, x_2);
lean_inc_ref(x_1);
x_19 = l_Lake_mkArgs(x_1, x_18, x_5, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec_ref(x_20);
x_24 = lean_array_push(x_15, x_1);
x_25 = l_Array_append___redArg(x_24, x_22);
lean_dec(x_22);
x_26 = l_Lake_compileLeanModule___closed__4;
x_27 = lean_box(0);
x_28 = l_Lake_compileO___closed__3;
x_29 = 0;
x_30 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_27);
lean_ctor_set(x_30, 4, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_14);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 1, x_29);
x_31 = l_Lake_proc(x_30, x_29, x_23, x_21);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec_ref(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_19, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_19, 0, x_37);
return x_19;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_41 = x_20;
} else {
 lean_dec_ref(x_20);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
x_49 = lean_io_error_to_string(x_47);
x_50 = 3;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
x_52 = lean_array_get_size(x_5);
x_53 = lean_array_push(x_5, x_51);
lean_ctor_set(x_11, 1, x_53);
lean_ctor_set(x_11, 0, x_52);
lean_ctor_set(x_7, 1, x_48);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_11, 0);
x_55 = lean_ctor_get(x_11, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_11);
x_56 = lean_io_error_to_string(x_54);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_5);
x_60 = lean_array_push(x_5, x_58);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_7, 1, x_55);
lean_ctor_set(x_7, 0, x_61);
return x_7;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_dec(x_7);
x_63 = l_Lake_removeFileIfExists(x_1, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lake_compileStaticLib___closed__1;
x_66 = 1;
if (x_4 == 0)
{
x_67 = x_65;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = l_Lake_compileStaticLib___closed__3;
x_67 = x_92;
goto block_91;
}
block_91:
{
size_t x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_array_size(x_2);
x_69 = 0;
x_70 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(x_68, x_69, x_2);
lean_inc_ref(x_1);
x_71 = l_Lake_mkArgs(x_1, x_70, x_5, x_64);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec_ref(x_72);
x_76 = lean_array_push(x_67, x_1);
x_77 = l_Array_append___redArg(x_76, x_74);
lean_dec(x_74);
x_78 = l_Lake_compileLeanModule___closed__4;
x_79 = lean_box(0);
x_80 = l_Lake_compileO___closed__3;
x_81 = 0;
x_82 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_82, 0, x_78);
lean_ctor_set(x_82, 1, x_3);
lean_ctor_set(x_82, 2, x_77);
lean_ctor_set(x_82, 3, x_79);
lean_ctor_set(x_82, 4, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*5, x_66);
lean_ctor_set_uint8(x_82, sizeof(void*)*5 + 1, x_81);
x_83 = l_Lake_proc(x_82, x_81, x_75, x_73);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec_ref(x_67);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_85 = x_71;
} else {
 lean_dec_ref(x_71);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_72, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_72, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_88 = x_72;
} else {
 lean_dec_ref(x_72);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_63, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_63, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_95 = x_63;
} else {
 lean_dec_ref(x_63);
 x_95 = lean_box(0);
}
x_96 = lean_io_error_to_string(x_93);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_5);
x_100 = lean_array_push(x_5, x_98);
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_95;
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_94);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_7);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_7, 0);
x_105 = lean_ctor_get(x_7, 1);
x_106 = lean_io_error_to_string(x_104);
x_107 = 3;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_get_size(x_5);
x_110 = lean_array_push(x_5, x_108);
lean_ctor_set(x_7, 1, x_110);
lean_ctor_set(x_7, 0, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_7);
lean_ctor_set(x_111, 1, x_105);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_7, 0);
x_113 = lean_ctor_get(x_7, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_7);
x_114 = lean_io_error_to_string(x_112);
x_115 = 3;
x_116 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*1, x_115);
x_117 = lean_array_get_size(x_5);
x_118 = lean_array_push(x_5, x_116);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
return x_120;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Lake_compileStaticLib(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
static uint8_t _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isOSX;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MACOSX_DEPLOYMENT_TARGET", 24, 24);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("99.0", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
x_2 = l_Lake_compileLeanModule___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_compileO___closed__3;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
x_6 = lean_io_getenv(x_5, x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec_ref(x_7);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = l_Lake_compileO___closed__3;
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_Lake_compileO___closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
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
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_inc_ref(x_1);
x_8 = l_Lake_mkArgs(x_1, x_2, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lake_compileLeanModule___closed__4;
x_17 = l_Lake_compileSharedLib___closed__3;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Array_append___redArg(x_18, x_11);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = 1;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_22);
x_24 = l_Lake_proc(x_23, x_22, x_12, x_15);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_34 = x_9;
} else {
 lean_dec_ref(x_9);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_4);
x_44 = lean_array_push(x_4, x_42);
lean_ctor_set(x_6, 1, x_44);
lean_ctor_set(x_6, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_io_error_to_string(x_46);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_4);
x_52 = lean_array_push(x_4, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_inc_ref(x_1);
x_8 = l_Lake_mkArgs(x_1, x_2, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lake_compileLeanModule___closed__4;
x_17 = l_Lake_compileLeanModule___closed__17;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Array_append___redArg(x_18, x_11);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = 1;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_14);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_22);
x_24 = l_Lake_proc(x_23, x_22, x_12, x_15);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_34 = x_9;
} else {
 lean_dec_ref(x_9);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_6);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_4);
x_44 = lean_array_push(x_4, x_42);
lean_ctor_set(x_6, 1, x_44);
lean_ctor_set(x_6, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_48 = lean_io_error_to_string(x_46);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_4);
x_52 = lean_array_push(x_4, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_download(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_18; lean_object* x_19; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_System_FilePath_pathExists(x_2, x_5);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = l_Lake_createParentDirs(x_2, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_free_object(x_33);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec_ref(x_39);
x_18 = x_4;
x_19 = x_40;
goto block_32;
}
else
{
uint8_t x_41; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_io_error_to_string(x_42);
x_45 = 3;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = lean_array_get_size(x_4);
x_48 = lean_array_push(x_4, x_46);
lean_ctor_set(x_39, 1, x_48);
lean_ctor_set(x_39, 0, x_47);
lean_ctor_set(x_33, 1, x_43);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_39, 0);
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_39);
x_51 = lean_io_error_to_string(x_49);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_4);
x_55 = lean_array_push(x_4, x_53);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_33, 1, x_50);
lean_ctor_set(x_33, 0, x_56);
return x_33;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
lean_dec(x_33);
x_58 = l_Lake_createParentDirs(x_2, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_18 = x_4;
x_19 = x_59;
goto block_32;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_io_error_to_string(x_60);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_4);
x_67 = lean_array_push(x_4, x_65);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
return x_69;
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_33);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_33, 1);
x_72 = lean_ctor_get(x_33, 0);
lean_dec(x_72);
x_73 = lean_io_remove_file(x_2, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
lean_free_object(x_33);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_18 = x_4;
x_19 = x_74;
goto block_32;
}
else
{
uint8_t x_75; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_75 = !lean_is_exclusive(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 1);
x_78 = lean_io_error_to_string(x_76);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_4);
x_82 = lean_array_push(x_4, x_80);
lean_ctor_set(x_73, 1, x_82);
lean_ctor_set(x_73, 0, x_81);
lean_ctor_set(x_33, 1, x_77);
lean_ctor_set(x_33, 0, x_73);
return x_33;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_io_error_to_string(x_83);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_array_get_size(x_4);
x_89 = lean_array_push(x_4, x_87);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_33, 1, x_84);
lean_ctor_set(x_33, 0, x_90);
return x_33;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_33, 1);
lean_inc(x_91);
lean_dec(x_33);
x_92 = lean_io_remove_file(x_2, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_18 = x_4;
x_19 = x_93;
goto block_32;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
x_97 = lean_io_error_to_string(x_94);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_array_get_size(x_4);
x_101 = lean_array_push(x_4, x_99);
if (lean_is_scalar(x_96)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_96;
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
return x_103;
}
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
x_16 = l_Lake_proc(x_15, x_13, x_6, x_7);
return x_16;
}
block_32:
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
lean_dec(x_26);
x_6 = x_18;
x_7 = x_19;
x_8 = x_24;
goto block_17;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_26, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
x_6 = x_18;
x_7 = x_19;
x_8 = x_24;
goto block_17;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0(x_3, x_29, x_30, x_24);
x_6 = x_18;
x_7 = x_19;
x_8 = x_31;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_download(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_createDirAll(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_27; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_27 = l_Lake_untar___closed__3;
if (x_3 == 0)
{
x_8 = x_27;
x_9 = x_4;
goto block_26;
}
else
{
lean_object* x_28; 
x_28 = l_Lake_untar___closed__4;
x_8 = x_28;
x_9 = x_4;
goto block_26;
}
block_26:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_10 = l_Lake_compileLeanModule___closed__4;
x_11 = l_Lake_untar___closed__0;
x_12 = l_Lake_download___closed__3;
x_13 = l_Lake_untar___closed__1;
x_14 = l_Lake_untar___closed__2;
x_15 = lean_array_push(x_14, x_8);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_array_push(x_17, x_13);
x_19 = lean_array_push(x_18, x_2);
x_20 = lean_box(0);
x_21 = l_Lake_compileO___closed__3;
x_22 = 1;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_23);
x_25 = l_Lake_proc(x_24, x_22, x_9, x_7);
return x_25;
}
}
else
{
uint8_t x_29; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
x_32 = lean_io_error_to_string(x_30);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_4);
x_36 = lean_array_push(x_4, x_34);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_4);
x_44 = lean_array_push(x_4, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_39);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_untar(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exclude=", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0;
x_12 = lean_string_append(x_11, x_10);
lean_dec_ref(x_10);
x_13 = lean_array_push(x_4, x_12);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_13;
goto _start;
}
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
x_2 = l_Lake_mkArgs___closed__3;
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
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_19; 
x_19 = l_Lake_createParentDirs(x_2, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_46; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec_ref(x_19);
x_46 = l_Lake_tar___closed__8;
if (x_3 == 0)
{
x_21 = x_46;
x_22 = x_5;
goto block_45;
}
else
{
lean_object* x_47; 
x_47 = l_Lake_tar___closed__10;
x_21 = x_47;
x_22 = x_5;
goto block_45;
}
block_45:
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_23 = lean_array_size(x_4);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(x_4, x_23, x_24, x_21, x_22, x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lake_compileLeanModule___closed__4;
x_31 = l_Lake_untar___closed__0;
x_32 = l_Lake_untar___closed__1;
x_33 = l_Lake_tar___closed__0;
x_34 = l_Lake_tar___closed__1;
x_35 = lean_array_push(x_34, x_2);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_array_push(x_36, x_1);
x_38 = lean_array_push(x_37, x_33);
x_39 = l_Array_append___redArg(x_28, x_38);
lean_dec_ref(x_38);
x_40 = lean_box(0);
x_41 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
x_42 = 1;
if (x_41 == 0)
{
lean_object* x_43; 
x_43 = l_Lake_compileO___closed__3;
x_7 = x_27;
x_8 = x_29;
x_9 = x_39;
x_10 = x_42;
x_11 = x_30;
x_12 = x_40;
x_13 = x_31;
x_14 = x_43;
goto block_18;
}
else
{
lean_object* x_44; 
x_44 = l_Lake_tar___closed__6;
x_7 = x_27;
x_8 = x_29;
x_9 = x_39;
x_10 = x_42;
x_11 = x_30;
x_12 = x_40;
x_13 = x_31;
x_14 = x_44;
goto block_18;
}
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
x_51 = lean_io_error_to_string(x_49);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_get_size(x_5);
x_55 = lean_array_push(x_5, x_53);
lean_ctor_set(x_19, 1, x_55);
lean_ctor_set(x_19, 0, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_19);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_io_error_to_string(x_57);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_5);
x_63 = lean_array_push(x_5, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_58);
return x_65;
}
}
block_18:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_15);
x_17 = l_Lake_proc(x_16, x_10, x_8, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lake_tar(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec_ref(x_4);
return x_8;
}
}
lean_object* initialize_Lean_Setup(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Setup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__0);
l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__4___closed__1);
l_Lake_compileLeanModule___lam__0___closed__0 = _init_l_Lake_compileLeanModule___lam__0___closed__0();
lean_mark_persistent(l_Lake_compileLeanModule___lam__0___closed__0);
l_Lake_compileLeanModule___lam__0___closed__1 = _init_l_Lake_compileLeanModule___lam__0___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lam__0___closed__1);
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
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1);
l_Lake_mkArgs___closed__0 = _init_l_Lake_mkArgs___closed__0();
l_Lake_mkArgs___closed__1 = _init_l_Lake_mkArgs___closed__1();
lean_mark_persistent(l_Lake_mkArgs___closed__1);
l_Lake_mkArgs___closed__2 = _init_l_Lake_mkArgs___closed__2();
lean_mark_persistent(l_Lake_mkArgs___closed__2);
l_Lake_mkArgs___closed__3 = _init_l_Lake_mkArgs___closed__3();
lean_mark_persistent(l_Lake_mkArgs___closed__3);
l_Lake_compileStaticLib___closed__0 = _init_l_Lake_compileStaticLib___closed__0();
lean_mark_persistent(l_Lake_compileStaticLib___closed__0);
l_Lake_compileStaticLib___closed__1 = _init_l_Lake_compileStaticLib___closed__1();
lean_mark_persistent(l_Lake_compileStaticLib___closed__1);
l_Lake_compileStaticLib___closed__2 = _init_l_Lake_compileStaticLib___closed__2();
lean_mark_persistent(l_Lake_compileStaticLib___closed__2);
l_Lake_compileStaticLib___closed__3 = _init_l_Lake_compileStaticLib___closed__3();
lean_mark_persistent(l_Lake_compileStaticLib___closed__3);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0();
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4);
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5);
l_Lake_compileSharedLib___closed__0 = _init_l_Lake_compileSharedLib___closed__0();
lean_mark_persistent(l_Lake_compileSharedLib___closed__0);
l_Lake_compileSharedLib___closed__1 = _init_l_Lake_compileSharedLib___closed__1();
lean_mark_persistent(l_Lake_compileSharedLib___closed__1);
l_Lake_compileSharedLib___closed__2 = _init_l_Lake_compileSharedLib___closed__2();
lean_mark_persistent(l_Lake_compileSharedLib___closed__2);
l_Lake_compileSharedLib___closed__3 = _init_l_Lake_compileSharedLib___closed__3();
lean_mark_persistent(l_Lake_compileSharedLib___closed__3);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0);
l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1);
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
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0);
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
