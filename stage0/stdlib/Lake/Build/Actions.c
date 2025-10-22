// Lean compiler output
// Module: Lake.Build.Actions
// Imports: public import Lake.Util.Log import Lake.Config.Dynlib import Lake.Util.Proc import Lake.Util.NativeLib import Lake.Util.FilePath import Lake.Util.IO
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
static lean_object* l_Lake_download___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__8;
static lean_object* l_Lake_compileSharedLib___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__9;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__5;
static lean_object* l_Lake_compileLeanModule___closed__6;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_compileLeanModule_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__13;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0;
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
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__11;
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__4;
static lean_object* l_Lake_download___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__7;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__0;
lean_object* l_Lake_removeFileIfExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_compileLeanModule_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
static lean_object* l_Lake_tar___closed__8;
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__9;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkArgs___closed__3;
static lean_object* l_Lake_compileLeanModule___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__0;
lean_object* l_IO_Process_output(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__3;
static lean_object* l_Lake_compileSharedLib___closed__0;
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1;
static lean_object* l_Lake_compileLeanModule___closed__15;
static lean_object* l_Lake_download___closed__4;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__16;
static lean_object* l_Lake_untar___closed__2;
static uint8_t l_Lake_mkArgs___closed__0;
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_compileO___closed__0;
static lean_object* l_Lake_untar___closed__4;
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
static lean_object* l_Lake_tar___closed__6;
static lean_object* l_Lake_compileO___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lake_compileLeanModule_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
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
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
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
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_tar___closed__7;
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
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_compileLeanModule_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_68 = l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1;
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
x_11 = l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_363; 
x_275 = lean_ctor_get(x_5, 1);
lean_inc(x_275);
x_276 = lean_ctor_get(x_5, 4);
lean_inc(x_276);
x_277 = lean_ctor_get(x_5, 6);
lean_inc(x_277);
x_278 = lean_ctor_get(x_5, 7);
lean_inc(x_278);
lean_dec_ref(x_5);
x_363 = lean_array_push(x_6, x_1);
if (lean_obj_tag(x_275) == 0)
{
x_335 = x_363;
x_336 = x_9;
x_337 = x_10;
goto block_362;
}
else
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_275, 0);
lean_inc(x_364);
lean_dec_ref(x_275);
x_365 = l_Lake_createParentDirs(x_364, x_10);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec_ref(x_365);
x_367 = l_Lake_compileLeanModule___closed__17;
x_368 = lean_array_push(x_367, x_364);
x_369 = l_Array_append___redArg(x_363, x_368);
lean_dec_ref(x_368);
x_335 = x_369;
x_336 = x_9;
x_337 = x_366;
goto block_362;
}
else
{
uint8_t x_370; 
lean_dec(x_364);
lean_dec_ref(x_363);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_370 = !lean_is_exclusive(x_365);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_371 = lean_ctor_get(x_365, 0);
x_372 = lean_ctor_get(x_365, 1);
x_373 = lean_io_error_to_string(x_371);
x_374 = 3;
x_375 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set_uint8(x_375, sizeof(void*)*1, x_374);
x_376 = lean_array_get_size(x_9);
x_377 = lean_array_push(x_9, x_375);
lean_ctor_set(x_365, 1, x_377);
lean_ctor_set(x_365, 0, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_365);
lean_ctor_set(x_378, 1, x_372);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_379 = lean_ctor_get(x_365, 0);
x_380 = lean_ctor_get(x_365, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_365);
x_381 = lean_io_error_to_string(x_379);
x_382 = 3;
x_383 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set_uint8(x_383, sizeof(void*)*1, x_382);
x_384 = lean_array_get_size(x_9);
x_385 = lean_array_push(x_9, x_383);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_380);
return x_387;
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
block_274:
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
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_66 = l_Lake_compileLeanModule___closed__7;
x_67 = lean_box(0);
x_68 = l_String_splitAux___at___Lake_compileLeanModule_spec__2(x_61, x_64, x_64, x_67);
lean_dec_ref(x_61);
x_69 = l_List_foldlM___at___Lake_compileLeanModule_spec__3(x_2, x_66, x_68, x_56, x_59);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_string_utf8_byte_size(x_72);
x_75 = lean_nat_dec_eq(x_74, x_64);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1;
x_77 = lean_string_append(x_76, x_72);
lean_dec(x_72);
x_78 = 1;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_box(0);
x_81 = lean_array_push(x_73, x_79);
x_82 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_80, x_81, x_71);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_82;
goto block_22;
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_72);
x_83 = lean_box(0);
x_84 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_83, x_73, x_71);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_84;
goto block_22;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_61);
lean_dec_ref(x_2);
x_85 = lean_box(0);
x_86 = l_Lake_compileLeanModule___lam__0(x_60, x_62, x_85, x_56, x_59);
lean_dec_ref(x_62);
x_17 = x_52;
x_18 = x_86;
goto block_22;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_57, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_57, 1);
lean_inc(x_88);
lean_dec_ref(x_57);
x_89 = l_Lake_compileLeanModule___closed__8;
x_90 = lean_string_append(x_89, x_8);
lean_dec_ref(x_8);
x_91 = l_Lake_compileLeanModule___closed__9;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_io_error_to_string(x_87);
x_94 = lean_string_append(x_92, x_93);
lean_dec_ref(x_93);
x_95 = 3;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_array_push(x_56, x_96);
x_11 = x_52;
x_12 = x_97;
x_13 = x_88;
goto block_16;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_98 = lean_ctor_get(x_33, 1);
lean_inc(x_98);
lean_dec(x_33);
x_99 = l_Lake_compileLeanModule___closed__2;
x_100 = lean_array_push(x_99, x_4);
x_101 = l_Array_append___redArg(x_23, x_100);
lean_dec_ref(x_100);
x_102 = l_Lake_compileLeanModule___closed__3;
x_103 = lean_array_push(x_101, x_102);
x_104 = l_Lake_compileLeanModule___closed__4;
x_105 = lean_box(0);
x_106 = l_Lake_compileLeanModule___closed__5;
x_107 = l_System_SearchPath_toString(x_7);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lake_compileLeanModule___closed__6;
x_111 = lean_array_push(x_110, x_109);
x_112 = 1;
x_113 = 0;
lean_inc_ref(x_8);
x_114 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_8);
lean_ctor_set(x_114, 2, x_103);
lean_ctor_set(x_114, 3, x_105);
lean_ctor_set(x_114, 4, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*5, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*5 + 1, x_113);
x_115 = lean_array_get_size(x_24);
lean_inc_ref(x_114);
x_116 = l_Lake_mkCmdLog(x_114);
x_117 = 0;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
x_119 = lean_array_push(x_24, x_118);
x_120 = l_IO_Process_output(x_114, x_105, x_98);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint32_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec_ref(x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec_ref(x_120);
x_123 = lean_ctor_get_uint32(x_121, sizeof(void*)*2);
x_124 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc_ref(x_125);
lean_dec(x_121);
x_126 = lean_string_utf8_byte_size(x_124);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_nat_dec_eq(x_126, x_127);
lean_dec(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_129 = l_Lake_compileLeanModule___closed__7;
x_130 = lean_box(0);
x_131 = l_String_splitAux___at___Lake_compileLeanModule_spec__2(x_124, x_127, x_127, x_130);
lean_dec_ref(x_124);
x_132 = l_List_foldlM___at___Lake_compileLeanModule_spec__3(x_2, x_129, x_131, x_119, x_122);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_string_utf8_byte_size(x_135);
x_138 = lean_nat_dec_eq(x_137, x_127);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1;
x_140 = lean_string_append(x_139, x_135);
lean_dec(x_135);
x_141 = 1;
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_box(0);
x_144 = lean_array_push(x_136, x_142);
x_145 = l_Lake_compileLeanModule___lam__0(x_123, x_125, x_143, x_144, x_134);
lean_dec_ref(x_125);
x_17 = x_115;
x_18 = x_145;
goto block_22;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_135);
x_146 = lean_box(0);
x_147 = l_Lake_compileLeanModule___lam__0(x_123, x_125, x_146, x_136, x_134);
lean_dec_ref(x_125);
x_17 = x_115;
x_18 = x_147;
goto block_22;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_124);
lean_dec_ref(x_2);
x_148 = lean_box(0);
x_149 = l_Lake_compileLeanModule___lam__0(x_123, x_125, x_148, x_119, x_122);
lean_dec_ref(x_125);
x_17 = x_115;
x_18 = x_149;
goto block_22;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_2);
x_150 = lean_ctor_get(x_120, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_120, 1);
lean_inc(x_151);
lean_dec_ref(x_120);
x_152 = l_Lake_compileLeanModule___closed__8;
x_153 = lean_string_append(x_152, x_8);
lean_dec_ref(x_8);
x_154 = l_Lake_compileLeanModule___closed__9;
x_155 = lean_string_append(x_153, x_154);
x_156 = lean_io_error_to_string(x_150);
x_157 = lean_string_append(x_155, x_156);
lean_dec_ref(x_156);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_push(x_119, x_159);
x_11 = x_115;
x_12 = x_160;
x_13 = x_151;
goto block_16;
}
}
}
else
{
uint8_t x_161; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_161 = !lean_is_exclusive(x_33);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_33, 0);
x_163 = lean_ctor_get(x_33, 1);
x_164 = lean_io_error_to_string(x_162);
x_165 = 3;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = lean_array_get_size(x_24);
x_168 = lean_array_push(x_24, x_166);
lean_ctor_set(x_33, 1, x_168);
lean_ctor_set(x_33, 0, x_167);
lean_ctor_set(x_26, 1, x_163);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_33, 0);
x_170 = lean_ctor_get(x_33, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_33);
x_171 = lean_io_error_to_string(x_169);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_24);
x_175 = lean_array_push(x_24, x_173);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_26, 1, x_170);
lean_ctor_set(x_26, 0, x_176);
return x_26;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_26, 1);
lean_inc(x_177);
lean_dec(x_26);
x_178 = l_Lean_instToJsonModuleSetup_toJson(x_3);
x_179 = lean_unsigned_to_nat(80u);
x_180 = l_Lean_Json_pretty(x_178, x_179);
x_181 = l_IO_FS_writeFile(x_4, x_180, x_177);
lean_dec_ref(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = l_Lake_compileLeanModule___closed__2;
x_185 = lean_array_push(x_184, x_4);
x_186 = l_Array_append___redArg(x_23, x_185);
lean_dec_ref(x_185);
x_187 = l_Lake_compileLeanModule___closed__3;
x_188 = lean_array_push(x_186, x_187);
x_189 = l_Lake_compileLeanModule___closed__4;
x_190 = lean_box(0);
x_191 = l_Lake_compileLeanModule___closed__5;
x_192 = l_System_SearchPath_toString(x_7);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_183)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_183;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lake_compileLeanModule___closed__6;
x_196 = lean_array_push(x_195, x_194);
x_197 = 1;
x_198 = 0;
lean_inc_ref(x_8);
x_199 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_8);
lean_ctor_set(x_199, 2, x_188);
lean_ctor_set(x_199, 3, x_190);
lean_ctor_set(x_199, 4, x_196);
lean_ctor_set_uint8(x_199, sizeof(void*)*5, x_197);
lean_ctor_set_uint8(x_199, sizeof(void*)*5 + 1, x_198);
x_200 = lean_array_get_size(x_24);
lean_inc_ref(x_199);
x_201 = l_Lake_mkCmdLog(x_199);
x_202 = 0;
x_203 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_202);
x_204 = lean_array_push(x_24, x_203);
x_205 = l_IO_Process_output(x_199, x_190, x_182);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; uint32_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
lean_dec_ref(x_8);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec_ref(x_205);
x_208 = lean_ctor_get_uint32(x_206, sizeof(void*)*2);
x_209 = lean_ctor_get(x_206, 0);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_206, 1);
lean_inc_ref(x_210);
lean_dec(x_206);
x_211 = lean_string_utf8_byte_size(x_209);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_dec_eq(x_211, x_212);
lean_dec(x_211);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_214 = l_Lake_compileLeanModule___closed__7;
x_215 = lean_box(0);
x_216 = l_String_splitAux___at___Lake_compileLeanModule_spec__2(x_209, x_212, x_212, x_215);
lean_dec_ref(x_209);
x_217 = l_List_foldlM___at___Lake_compileLeanModule_spec__3(x_2, x_214, x_216, x_204, x_207);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec_ref(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_string_utf8_byte_size(x_220);
x_223 = lean_nat_dec_eq(x_222, x_212);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1;
x_225 = lean_string_append(x_224, x_220);
lean_dec(x_220);
x_226 = 1;
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_226);
x_228 = lean_box(0);
x_229 = lean_array_push(x_221, x_227);
x_230 = l_Lake_compileLeanModule___lam__0(x_208, x_210, x_228, x_229, x_219);
lean_dec_ref(x_210);
x_17 = x_200;
x_18 = x_230;
goto block_22;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_220);
x_231 = lean_box(0);
x_232 = l_Lake_compileLeanModule___lam__0(x_208, x_210, x_231, x_221, x_219);
lean_dec_ref(x_210);
x_17 = x_200;
x_18 = x_232;
goto block_22;
}
}
else
{
lean_object* x_233; lean_object* x_234; 
lean_dec_ref(x_209);
lean_dec_ref(x_2);
x_233 = lean_box(0);
x_234 = l_Lake_compileLeanModule___lam__0(x_208, x_210, x_233, x_204, x_207);
lean_dec_ref(x_210);
x_17 = x_200;
x_18 = x_234;
goto block_22;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec_ref(x_2);
x_235 = lean_ctor_get(x_205, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_205, 1);
lean_inc(x_236);
lean_dec_ref(x_205);
x_237 = l_Lake_compileLeanModule___closed__8;
x_238 = lean_string_append(x_237, x_8);
lean_dec_ref(x_8);
x_239 = l_Lake_compileLeanModule___closed__9;
x_240 = lean_string_append(x_238, x_239);
x_241 = lean_io_error_to_string(x_235);
x_242 = lean_string_append(x_240, x_241);
lean_dec_ref(x_241);
x_243 = 3;
x_244 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_243);
x_245 = lean_array_push(x_204, x_244);
x_11 = x_200;
x_12 = x_245;
x_13 = x_236;
goto block_16;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_246 = lean_ctor_get(x_181, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_181, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_248 = x_181;
} else {
 lean_dec_ref(x_181);
 x_248 = lean_box(0);
}
x_249 = lean_io_error_to_string(x_246);
x_250 = 3;
x_251 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set_uint8(x_251, sizeof(void*)*1, x_250);
x_252 = lean_array_get_size(x_24);
x_253 = lean_array_push(x_24, x_251);
if (lean_is_scalar(x_248)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_248;
}
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_247);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec_ref(x_23);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_256 = !lean_is_exclusive(x_26);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_257 = lean_ctor_get(x_26, 0);
x_258 = lean_ctor_get(x_26, 1);
x_259 = lean_io_error_to_string(x_257);
x_260 = 3;
x_261 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_260);
x_262 = lean_array_get_size(x_24);
x_263 = lean_array_push(x_24, x_261);
lean_ctor_set(x_26, 1, x_263);
lean_ctor_set(x_26, 0, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_26);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_265 = lean_ctor_get(x_26, 0);
x_266 = lean_ctor_get(x_26, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_26);
x_267 = lean_io_error_to_string(x_265);
x_268 = 3;
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_268);
x_270 = lean_array_get_size(x_24);
x_271 = lean_array_push(x_24, x_269);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_266);
return x_273;
}
}
}
block_306:
{
if (lean_obj_tag(x_278) == 0)
{
x_23 = x_279;
x_24 = x_280;
x_25 = x_281;
goto block_274;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
lean_dec_ref(x_278);
x_283 = l_Lake_createParentDirs(x_282, x_281);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec_ref(x_283);
x_285 = l_Lake_compileLeanModule___closed__11;
x_286 = lean_array_push(x_285, x_282);
x_287 = l_Array_append___redArg(x_279, x_286);
lean_dec_ref(x_286);
x_23 = x_287;
x_24 = x_280;
x_25 = x_284;
goto block_274;
}
else
{
uint8_t x_288; 
lean_dec(x_282);
lean_dec_ref(x_279);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_288 = !lean_is_exclusive(x_283);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_289 = lean_ctor_get(x_283, 0);
x_290 = lean_ctor_get(x_283, 1);
x_291 = lean_io_error_to_string(x_289);
x_292 = 3;
x_293 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*1, x_292);
x_294 = lean_array_get_size(x_280);
x_295 = lean_array_push(x_280, x_293);
lean_ctor_set(x_283, 1, x_295);
lean_ctor_set(x_283, 0, x_294);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_283);
lean_ctor_set(x_296, 1, x_290);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_297 = lean_ctor_get(x_283, 0);
x_298 = lean_ctor_get(x_283, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_283);
x_299 = lean_io_error_to_string(x_297);
x_300 = 3;
x_301 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_300);
x_302 = lean_array_get_size(x_280);
x_303 = lean_array_push(x_280, x_301);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_298);
return x_305;
}
}
}
}
block_334:
{
if (lean_obj_tag(x_277) == 0)
{
x_279 = x_307;
x_280 = x_308;
x_281 = x_309;
goto block_306;
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_277, 0);
lean_inc(x_310);
lean_dec_ref(x_277);
x_311 = l_Lake_createParentDirs(x_310, x_309);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec_ref(x_311);
x_313 = l_Lake_compileLeanModule___closed__13;
x_314 = lean_array_push(x_313, x_310);
x_315 = l_Array_append___redArg(x_307, x_314);
lean_dec_ref(x_314);
x_279 = x_315;
x_280 = x_308;
x_281 = x_312;
goto block_306;
}
else
{
uint8_t x_316; 
lean_dec(x_310);
lean_dec_ref(x_307);
lean_dec(x_278);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_316 = !lean_is_exclusive(x_311);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = lean_ctor_get(x_311, 0);
x_318 = lean_ctor_get(x_311, 1);
x_319 = lean_io_error_to_string(x_317);
x_320 = 3;
x_321 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_320);
x_322 = lean_array_get_size(x_308);
x_323 = lean_array_push(x_308, x_321);
lean_ctor_set(x_311, 1, x_323);
lean_ctor_set(x_311, 0, x_322);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_311);
lean_ctor_set(x_324, 1, x_318);
return x_324;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_325 = lean_ctor_get(x_311, 0);
x_326 = lean_ctor_get(x_311, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_311);
x_327 = lean_io_error_to_string(x_325);
x_328 = 3;
x_329 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*1, x_328);
x_330 = lean_array_get_size(x_308);
x_331 = lean_array_push(x_308, x_329);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_326);
return x_333;
}
}
}
}
block_362:
{
if (lean_obj_tag(x_276) == 0)
{
x_307 = x_335;
x_308 = x_336;
x_309 = x_337;
goto block_334;
}
else
{
lean_object* x_338; lean_object* x_339; 
x_338 = lean_ctor_get(x_276, 0);
lean_inc(x_338);
lean_dec_ref(x_276);
x_339 = l_Lake_createParentDirs(x_338, x_337);
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec_ref(x_339);
x_341 = l_Lake_compileLeanModule___closed__15;
x_342 = lean_array_push(x_341, x_338);
x_343 = l_Array_append___redArg(x_335, x_342);
lean_dec_ref(x_342);
x_307 = x_343;
x_308 = x_336;
x_309 = x_340;
goto block_334;
}
else
{
uint8_t x_344; 
lean_dec(x_338);
lean_dec_ref(x_335);
lean_dec(x_278);
lean_dec(x_277);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_344 = !lean_is_exclusive(x_339);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_345 = lean_ctor_get(x_339, 0);
x_346 = lean_ctor_get(x_339, 1);
x_347 = lean_io_error_to_string(x_345);
x_348 = 3;
x_349 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*1, x_348);
x_350 = lean_array_get_size(x_336);
x_351 = lean_array_push(x_336, x_349);
lean_ctor_set(x_339, 1, x_351);
lean_ctor_set(x_339, 0, x_350);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_339);
lean_ctor_set(x_352, 1, x_346);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_353 = lean_ctor_get(x_339, 0);
x_354 = lean_ctor_get(x_339, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_339);
x_355 = lean_io_error_to_string(x_353);
x_356 = 3;
x_357 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set_uint8(x_357, sizeof(void*)*1, x_356);
x_358 = lean_array_get_size(x_336);
x_359 = lean_array_push(x_336, x_357);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_354);
return x_361;
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
LEAN_EXPORT lean_object* l_String_splitAux___at___Lake_compileLeanModule_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___Lake_compileLeanModule_spec__2(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_5;
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
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
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
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
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
l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__0);
l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__3___closed__1);
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
