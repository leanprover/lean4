// Lean compiler output
// Module: Lake.Build.Actions
// Imports: Lake.Util.Proc Lake.Util.NativeLib Lake.Util.IO
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
static lean_object* l_Lake_compileLeanModule___lambda__4___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__1;
static lean_object* l_Lake_tar___lambda__1___closed__5;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__5___closed__1;
static lean_object* l_Lake_download___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__4___closed__1;
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_untar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__3___closed__2;
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__5;
static lean_object* l_Lake_compileLeanModule___lambda__6___closed__1;
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2;
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3671_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___lambda__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__4;
static lean_object* l_Lake_tar___lambda__1___closed__3;
static lean_object* l_Lake_compileLeanModule___closed__2;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__4;
static lean_object* l_Lake_untar___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_tar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_LogLevel_ofMessageSeverity(uint8_t);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Lake_tar___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_untar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__1;
LEAN_EXPORT lean_object* l_Lake_download___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__5;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1;
static lean_object* l_Lake_compileO___closed__1;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_compileLeanModule___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_compileLeanModule___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_tar___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__7___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__4___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_untar___closed__1;
static lean_object* l_Lake_tar___lambda__1___closed__4;
static lean_object* l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--load-dynlib", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_13 = lean_array_uget(x_4, x_6);
lean_inc(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_mk(x_16);
x_18 = l_Array_append___rarg(x_7, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
goto _start;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--plugin", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_13 = lean_array_uget(x_4, x_6);
lean_inc(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_mk(x_16);
x_18 = l_Array_append___rarg(x_7, x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
goto _start;
}
}
}
static lean_object* _init_l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_5, x_6, x_7);
x_9 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_5, x_8, x_6);
x_10 = lean_string_utf8_extract(x_5, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_nat_dec_eq(x_11, x_7);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
x_14 = l_Lake_LogLevel_ofMessageSeverity(x_13);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_box(0);
if (x_12 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_19 = lean_string_append(x_18, x_10);
lean_dec(x_10);
x_20 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_ctor_get(x_4, 4);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_string_utf8_byte_size(x_22);
x_24 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_22, x_23, x_7);
x_25 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_22, x_24, x_23);
x_26 = lean_string_utf8_extract(x_22, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
x_27 = lean_string_append(x_21, x_26);
lean_dec(x_26);
x_28 = lean_string_append(x_27, x_18);
x_29 = l_Lean_mkErrorStringWithPos(x_15, x_16, x_28, x_17);
lean_dec(x_28);
lean_dec(x_15);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_14);
x_31 = lean_array_push(x_2, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
x_35 = lean_ctor_get(x_4, 4);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_string_utf8_byte_size(x_35);
x_37 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_35, x_36, x_7);
x_38 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_35, x_37, x_36);
x_39 = lean_string_utf8_extract(x_35, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
x_40 = l_Lean_mkErrorStringWithPos(x_15, x_16, x_39, x_17);
lean_dec(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_14);
x_42 = lean_array_push(x_2, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3(x_2, x_4, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1(x_1, x_11, x_12, x_10);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1(x_1, x_14, x_4, x_5);
return x_15;
}
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_25; lean_object* x_26; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_25 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2;
lean_inc(x_8);
x_26 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_25, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_26);
x_27 = lean_box(0);
x_10 = x_27;
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3671_(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_29);
x_30 = lean_box(0);
x_10 = x_30;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_8);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_string_utf8_byte_size(x_2);
x_33 = lean_nat_dec_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3;
x_35 = lean_string_append(x_34, x_2);
x_36 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = 1;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_push(x_4, x_39);
x_41 = lean_box(0);
x_42 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2(x_2, x_31, x_41, x_40, x_5);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_2 = x_45;
x_3 = x_9;
x_4 = x_46;
x_5 = x_44;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_box(0);
x_49 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2(x_2, x_31, x_48, x_4, x_5);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_2 = x_52;
x_3 = x_9;
x_4 = x_53;
x_5 = x_51;
goto _start;
}
}
}
block_24:
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_10);
x_11 = lean_string_utf8_byte_size(x_2);
x_12 = lean_nat_dec_eq(x_11, x_1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_append(x_2, x_8);
lean_dec(x_8);
x_14 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_2 = x_15;
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_string_utf8_byte_size(x_8);
x_18 = lean_nat_dec_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_string_append(x_2, x_8);
lean_dec(x_8);
x_20 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_2 = x_21;
x_3 = x_9;
goto _start;
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
static lean_object* _init_l_Lake_compileLeanModule___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean exited with code ", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint32_t x_5; uint32_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get_uint32(x_1, sizeof(void*)*2);
x_6 = 0;
x_7 = lean_uint32_dec_eq(x_5, x_6);
x_8 = l_instDecidableNot___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_uint32_to_nat(x_5);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = l_Lake_compileLeanModule___lambda__1___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = 3;
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_18);
x_20 = lean_array_get_size(x_3);
x_21 = lean_array_push(x_3, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stderr:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_byte_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_5, x_6, x_7);
x_10 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_5, x_9, x_6);
x_11 = lean_string_utf8_extract(x_5, x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_Lake_compileLeanModule___lambda__2___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
x_18 = lean_array_push(x_3, x_17);
x_19 = lean_box(0);
x_20 = l_Lake_compileLeanModule___lambda__1(x_1, x_19, x_18, x_4);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_box(0);
x_22 = l_Lake_compileLeanModule___lambda__1(x_1, x_21, x_3, x_4);
return x_22;
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to execute '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_51; 
x_51 = l_IO_Process_output(x_1, x_5);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 0, x_55);
x_6 = x_51;
x_7 = x_54;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_4);
x_6 = x_59;
x_7 = x_57;
goto block_50;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_51, 0);
x_62 = lean_ctor_get(x_51, 1);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_tag(x_51, 0);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_51, 0, x_63);
x_6 = x_51;
x_7 = x_62;
goto block_50;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_4);
x_6 = x_67;
x_7 = x_65;
goto block_50;
}
}
block_50:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lake_compileLeanModule___lambda__3___closed__1;
x_14 = lean_string_append(x_13, x_2);
x_15 = l_Lake_compileLeanModule___lambda__3___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_io_error_to_string(x_12);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_10);
x_24 = lean_array_push(x_10, x_22);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_24);
lean_ctor_set(x_6, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_dec(x_6);
x_27 = lean_ctor_get(x_8, 0);
lean_inc(x_27);
lean_dec(x_8);
x_28 = l_Lake_compileLeanModule___lambda__3___closed__1;
x_29 = lean_string_append(x_28, x_2);
x_30 = l_Lake_compileLeanModule___lambda__3___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_io_error_to_string(x_27);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_26);
x_39 = lean_array_push(x_26, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_7);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_6, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_8, 0);
lean_inc(x_44);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_7);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_dec(x_6);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
}
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--json", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__4___closed__2() {
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
static lean_object* _init_l_Lake_compileLeanModule___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_box(0);
x_11 = lean_array_size(x_1);
x_12 = 0;
lean_inc(x_2);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1(x_1, x_2, x_10, x_1, x_11, x_12, x_6, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_array_size(x_3);
lean_inc(x_2);
x_20 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(x_3, x_2, x_10, x_3, x_19, x_12, x_17, x_18, x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
x_27 = l_Lake_compileLeanModule___lambda__4___closed__1;
x_28 = lean_array_push(x_25, x_27);
x_29 = lean_box(0);
x_30 = l_System_SearchPath_toString(x_4);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lake_compileLeanModule___lambda__4___closed__3;
lean_ctor_set(x_21, 1, x_31);
lean_ctor_set(x_21, 0, x_32);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_21);
x_33 = lean_array_mk(x_14);
x_34 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_35 = 0;
lean_inc(x_5);
x_36 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*5, x_35);
x_37 = lean_array_get_size(x_26);
lean_inc(x_36);
x_122 = l_Lake_mkCmdLog(x_36);
x_123 = 0;
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_123);
x_125 = lean_array_push(x_26, x_124);
x_126 = lean_box(0);
x_127 = l_Lake_compileLeanModule___lambda__3(x_36, x_5, x_126, x_125, x_22);
lean_dec(x_5);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_38 = x_128;
x_39 = x_129;
goto block_121;
}
else
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_128, 0);
lean_dec(x_132);
lean_inc(x_37);
lean_ctor_set(x_128, 0, x_37);
x_38 = x_128;
x_39 = x_130;
goto block_121;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_dec(x_128);
lean_inc(x_37);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_37);
lean_ctor_set(x_134, 1, x_133);
x_38 = x_134;
x_39 = x_130;
goto block_121;
}
}
block_121:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_23);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_string_utf8_byte_size(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_46 = l_String_split___at_Lean_stringToMessageData___spec__1(x_42);
lean_dec(x_42);
x_47 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_48 = l_List_foldlM___at_Lake_compileLeanModule___spec__4(x_44, x_47, x_46, x_41, x_39);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_string_utf8_byte_size(x_51);
x_54 = lean_nat_dec_eq(x_53, x_44);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3;
x_56 = lean_string_append(x_55, x_51);
lean_dec(x_51);
x_57 = lean_string_append(x_56, x_47);
x_58 = 1;
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
x_60 = lean_array_push(x_52, x_59);
x_61 = lean_box(0);
x_62 = l_Lake_compileLeanModule___lambda__2(x_40, x_61, x_60, x_50);
lean_dec(x_40);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
lean_dec(x_37);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_62, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_63, 0);
lean_dec(x_71);
lean_ctor_set(x_63, 0, x_37);
return x_62;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_37);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_62, 0, x_73);
return x_62;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_76 = x_63;
} else {
 lean_dec_ref(x_63);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_37);
lean_ctor_set(x_77, 1, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_74);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_51);
x_79 = lean_box(0);
x_80 = l_Lake_compileLeanModule___lambda__2(x_40, x_79, x_52, x_50);
lean_dec(x_40);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
lean_dec(x_37);
x_82 = !lean_is_exclusive(x_80);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_80, 0);
lean_dec(x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_80, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_81, 0);
lean_dec(x_89);
lean_ctor_set(x_81, 0, x_37);
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_37);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_80, 0, x_91);
return x_80;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_dec(x_80);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_37);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_92);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_42);
x_97 = lean_box(0);
x_98 = l_Lake_compileLeanModule___lambda__2(x_40, x_97, x_41, x_39);
lean_dec(x_40);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
lean_dec(x_37);
x_100 = !lean_is_exclusive(x_98);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_98, 0);
lean_dec(x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_98, 1);
lean_inc(x_102);
lean_dec(x_98);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_99);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_98);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_98, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_99);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_99, 0);
lean_dec(x_107);
lean_ctor_set(x_99, 0, x_37);
return x_98;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec(x_99);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_37);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set(x_98, 0, x_109);
return x_98;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_98, 1);
lean_inc(x_110);
lean_dec(x_98);
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_112 = x_99;
} else {
 lean_dec_ref(x_99);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_37);
lean_ctor_set(x_113, 1, x_111);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_38);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_38, 0);
lean_dec(x_116);
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_23)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_23;
}
lean_ctor_set(x_117, 0, x_38);
lean_ctor_set(x_117, 1, x_39);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_38, 1);
lean_inc(x_118);
lean_dec(x_38);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_37);
lean_ctor_set(x_119, 1, x_118);
if (lean_is_scalar(x_23)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_23;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_39);
return x_120;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_135 = lean_ctor_get(x_21, 0);
x_136 = lean_ctor_get(x_21, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_21);
x_137 = l_Lake_compileLeanModule___lambda__4___closed__1;
x_138 = lean_array_push(x_135, x_137);
x_139 = lean_box(0);
x_140 = l_System_SearchPath_toString(x_4);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = l_Lake_compileLeanModule___lambda__4___closed__3;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_143);
x_144 = lean_array_mk(x_14);
x_145 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_146 = 0;
lean_inc(x_5);
x_147 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_5);
lean_ctor_set(x_147, 2, x_138);
lean_ctor_set(x_147, 3, x_139);
lean_ctor_set(x_147, 4, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*5, x_146);
x_148 = lean_array_get_size(x_136);
lean_inc(x_147);
x_213 = l_Lake_mkCmdLog(x_147);
x_214 = 0;
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_214);
x_216 = lean_array_push(x_136, x_215);
x_217 = lean_box(0);
x_218 = l_Lake_compileLeanModule___lambda__3(x_147, x_5, x_217, x_216, x_22);
lean_dec(x_5);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_149 = x_219;
x_150 = x_220;
goto block_212;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
lean_inc(x_148);
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_148);
lean_ctor_set(x_224, 1, x_222);
x_149 = x_224;
x_150 = x_221;
goto block_212;
}
block_212:
{
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_23);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
lean_dec(x_149);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_string_utf8_byte_size(x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_nat_dec_eq(x_154, x_155);
lean_dec(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_157 = l_String_split___at_Lean_stringToMessageData___spec__1(x_153);
lean_dec(x_153);
x_158 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_159 = l_List_foldlM___at_Lake_compileLeanModule___spec__4(x_155, x_158, x_157, x_152, x_150);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = lean_string_utf8_byte_size(x_162);
x_165 = lean_nat_dec_eq(x_164, x_155);
lean_dec(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_166 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3;
x_167 = lean_string_append(x_166, x_162);
lean_dec(x_162);
x_168 = lean_string_append(x_167, x_158);
x_169 = 1;
x_170 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_169);
x_171 = lean_array_push(x_163, x_170);
x_172 = lean_box(0);
x_173 = l_Lake_compileLeanModule___lambda__2(x_151, x_172, x_171, x_161);
lean_dec(x_151);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_148);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_179 = x_173;
} else {
 lean_dec_ref(x_173);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_174, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_148);
lean_ctor_set(x_182, 1, x_180);
if (lean_is_scalar(x_179)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_179;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_178);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_162);
x_184 = lean_box(0);
x_185 = l_Lake_compileLeanModule___lambda__2(x_151, x_184, x_163, x_161);
lean_dec(x_151);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_148);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_191 = x_185;
} else {
 lean_dec_ref(x_185);
 x_191 = lean_box(0);
}
x_192 = lean_ctor_get(x_186, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_193 = x_186;
} else {
 lean_dec_ref(x_186);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_148);
lean_ctor_set(x_194, 1, x_192);
if (lean_is_scalar(x_191)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_191;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_153);
x_196 = lean_box(0);
x_197 = l_Lake_compileLeanModule___lambda__2(x_151, x_196, x_152, x_150);
lean_dec(x_151);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_148);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(0, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_203 = x_197;
} else {
 lean_dec_ref(x_197);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_198, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_205 = x_198;
} else {
 lean_dec_ref(x_198);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_148);
lean_ctor_set(x_206, 1, x_204);
if (lean_is_scalar(x_203)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_203;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_202);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_149, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_209 = x_149;
} else {
 lean_dec_ref(x_149);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_148);
lean_ctor_set(x_210, 1, x_208);
if (lean_is_scalar(x_23)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_23;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_150);
return x_211;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; size_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_225 = lean_ctor_get(x_14, 0);
x_226 = lean_ctor_get(x_14, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_14);
x_227 = lean_array_size(x_3);
lean_inc(x_2);
x_228 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(x_3, x_2, x_10, x_3, x_227, x_12, x_225, x_226, x_15);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 x_234 = x_229;
} else {
 lean_dec_ref(x_229);
 x_234 = lean_box(0);
}
x_235 = l_Lake_compileLeanModule___lambda__4___closed__1;
x_236 = lean_array_push(x_232, x_235);
x_237 = lean_box(0);
x_238 = l_System_SearchPath_toString(x_4);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = l_Lake_compileLeanModule___lambda__4___closed__3;
if (lean_is_scalar(x_234)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_234;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_2);
x_243 = lean_array_mk(x_242);
x_244 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_245 = 0;
lean_inc(x_5);
x_246 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_5);
lean_ctor_set(x_246, 2, x_236);
lean_ctor_set(x_246, 3, x_237);
lean_ctor_set(x_246, 4, x_243);
lean_ctor_set_uint8(x_246, sizeof(void*)*5, x_245);
x_247 = lean_array_get_size(x_233);
lean_inc(x_246);
x_312 = l_Lake_mkCmdLog(x_246);
x_313 = 0;
x_314 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*1, x_313);
x_315 = lean_array_push(x_233, x_314);
x_316 = lean_box(0);
x_317 = l_Lake_compileLeanModule___lambda__3(x_246, x_5, x_316, x_315, x_230);
lean_dec(x_5);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; 
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_248 = x_318;
x_249 = x_319;
goto block_311;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_ctor_get(x_318, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_322 = x_318;
} else {
 lean_dec_ref(x_318);
 x_322 = lean_box(0);
}
lean_inc(x_247);
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_247);
lean_ctor_set(x_323, 1, x_321);
x_248 = x_323;
x_249 = x_320;
goto block_311;
}
block_311:
{
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_231);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_string_utf8_byte_size(x_252);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_nat_dec_eq(x_253, x_254);
lean_dec(x_253);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_256 = l_String_split___at_Lean_stringToMessageData___spec__1(x_252);
lean_dec(x_252);
x_257 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_258 = l_List_foldlM___at_Lake_compileLeanModule___spec__4(x_254, x_257, x_256, x_251, x_249);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_263 = lean_string_utf8_byte_size(x_261);
x_264 = lean_nat_dec_eq(x_263, x_254);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_265 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3;
x_266 = lean_string_append(x_265, x_261);
lean_dec(x_261);
x_267 = lean_string_append(x_266, x_257);
x_268 = 1;
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_268);
x_270 = lean_array_push(x_262, x_269);
x_271 = lean_box(0);
x_272 = l_Lake_compileLeanModule___lambda__2(x_250, x_271, x_270, x_260);
lean_dec(x_250);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_247);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_273, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_247);
lean_ctor_set(x_281, 1, x_279);
if (lean_is_scalar(x_278)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_278;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_277);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_261);
x_283 = lean_box(0);
x_284 = l_Lake_compileLeanModule___lambda__2(x_250, x_283, x_262, x_260);
lean_dec(x_250);
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_247);
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_287 = x_284;
} else {
 lean_dec_ref(x_284);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_289 = lean_ctor_get(x_284, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_290 = x_284;
} else {
 lean_dec_ref(x_284);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_247);
lean_ctor_set(x_293, 1, x_291);
if (lean_is_scalar(x_290)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_290;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_289);
return x_294;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_252);
x_295 = lean_box(0);
x_296 = l_Lake_compileLeanModule___lambda__2(x_250, x_295, x_251, x_249);
lean_dec(x_250);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_247);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_ctor_get(x_296, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_302 = x_296;
} else {
 lean_dec_ref(x_296);
 x_302 = lean_box(0);
}
x_303 = lean_ctor_get(x_297, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_304 = x_297;
} else {
 lean_dec_ref(x_297);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_247);
lean_ctor_set(x_305, 1, x_303);
if (lean_is_scalar(x_302)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_302;
}
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_301);
return x_306;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = lean_ctor_get(x_248, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_308 = x_248;
} else {
 lean_dec_ref(x_248);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_247);
lean_ctor_set(x_309, 1, x_307);
if (lean_is_scalar(x_231)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_231;
}
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_249);
return x_310;
}
}
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-b", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lake_compileLeanModule___lambda__4(x_1, x_2, x_3, x_4, x_5, x_7, x_11, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = l_Lake_createParentDirs(x_13, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Lake_compileLeanModule___lambda__5___closed__1;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_array_mk(x_18);
x_20 = l_Array_append___rarg(x_7, x_19);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = l_Lake_compileLeanModule___lambda__4(x_1, x_2, x_3, x_4, x_5, x_20, x_21, x_9, x_15);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_io_error_to_string(x_24);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_9);
x_29 = lean_array_push(x_9, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_9);
x_37 = lean_array_push(x_9, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-c", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lake_compileLeanModule___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_12, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = l_Lake_createParentDirs(x_14, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_2);
lean_inc(x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_2);
x_18 = l_Lake_compileLeanModule___lambda__6___closed__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_mk(x_19);
x_21 = l_Array_append___rarg(x_8, x_20);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = l_Lake_compileLeanModule___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_21, x_22, x_10, x_16);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_10);
x_30 = lean_array_push(x_10, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_io_error_to_string(x_32);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_10);
x_38 = lean_array_push(x_10, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lake_compileLeanModule___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-i", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lake_compileLeanModule___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_13, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = l_Lake_createParentDirs(x_15, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_2);
lean_inc(x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_2);
x_19 = l_Lake_compileLeanModule___lambda__7___closed__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_mk(x_20);
x_22 = l_Array_append___rarg(x_9, x_21);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = l_Lake_compileLeanModule___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_22, x_23, x_11, x_17);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_11);
x_31 = lean_array_push(x_11, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_io_error_to_string(x_33);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_11);
x_39 = lean_array_push(x_11, x_37);
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
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-R", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-o", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lake_compileLeanModule___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = l_Array_append___rarg(x_10, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lake_compileLeanModule___lambda__7(x_8, x_14, x_9, x_6, x_11, x_5, x_4, x_3, x_20, x_21, x_12, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = l_Lake_createParentDirs(x_23, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_23);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_14);
x_27 = l_Lake_compileLeanModule___closed__2;
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_array_mk(x_28);
x_30 = l_Array_append___rarg(x_20, x_29);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = l_Lake_compileLeanModule___lambda__7(x_8, x_14, x_9, x_6, x_11, x_5, x_4, x_3, x_30, x_31, x_12, x_25);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_6);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_io_error_to_string(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_12);
x_39 = lean_array_push(x_12, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 0, x_40);
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_io_error_to_string(x_41);
x_44 = 3;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
x_46 = lean_array_get_size(x_12);
x_47 = lean_array_push(x_12, x_45);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at_Lake_compileLeanModule___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at_Lake_compileLeanModule___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_compileLeanModule___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_compileLeanModule___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_compileLeanModule___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lake_compileLeanModule___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lake_compileLeanModule___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lake_compileLeanModule___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lake_compileLeanModule___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lake_compileLeanModule(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l_Lake_compileO___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_compileLeanModule___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lake_compileLeanModule___lambda__6___closed__1;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_array_mk(x_15);
x_17 = l_Array_append___rarg(x_16, x_3);
x_18 = lean_box(0);
x_19 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_20 = l_Lake_compileO___closed__1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_21);
x_23 = l_Lake_proc(x_22, x_21, x_5, x_8);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_5);
x_30 = lean_array_push(x_5, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_io_error_to_string(x_32);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_5);
x_38 = lean_array_push(x_5, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lake_compileStaticLib___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rcs", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lake_compileStaticLib___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_array_mk(x_11);
x_13 = lean_array_size(x_2);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_13, x_14, x_2);
x_16 = l_Array_append___rarg(x_12, x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_19 = l_Lake_compileO___closed__1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_20);
x_22 = l_Lake_proc(x_21, x_20, x_4, x_7);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_6, 0);
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
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_30);
return x_6;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_6, 0);
x_32 = lean_ctor_get(x_6, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_6);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_4);
x_37 = lean_array_push(x_4, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_4, x_5, x_3);
return x_6;
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
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_compileO___closed__1;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
x_6 = lean_io_getenv(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
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
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = l_Lake_compileO___closed__1;
lean_ctor_set(x_6, 0, x_16);
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_Lake_compileO___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_6);
if (x_20 == 0)
{
return x_6;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-shared", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lake_compileLeanModule___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lake_compileSharedLib___closed__1;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_mk(x_16);
x_18 = l_Array_append___rarg(x_17, x_2);
x_19 = lean_box(0);
x_20 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_9);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_21);
x_23 = l_Lake_proc(x_22, x_21, x_4, x_10);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_io_error_to_string(x_29);
x_31 = 3;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_get_size(x_4);
x_34 = lean_array_push(x_4, x_32);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_io_error_to_string(x_36);
x_39 = 3;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_array_get_size(x_4);
x_42 = lean_array_push(x_4, x_40);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileSharedLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_compileSharedLib(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_39; 
x_39 = l_Lake_createParentDirs(x_1, x_6);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
lean_ctor_set(x_39, 1, x_5);
x_7 = x_39;
x_8 = x_41;
goto block_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_5);
x_7 = x_44;
x_8 = x_43;
goto block_38;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_39, 0);
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_io_error_to_string(x_46);
x_49 = 3;
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_49);
x_51 = lean_array_get_size(x_5);
x_52 = lean_array_push(x_5, x_50);
lean_ctor_set(x_39, 1, x_52);
lean_ctor_set(x_39, 0, x_51);
x_7 = x_39;
x_8 = x_47;
goto block_38;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_io_error_to_string(x_53);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_5);
x_59 = lean_array_push(x_5, x_57);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_7 = x_60;
x_8 = x_54;
goto block_38;
}
}
block_38:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lake_compileLeanModule___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_mk(x_16);
x_18 = lean_array_size(x_2);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_18, x_19, x_2);
x_21 = l_Array_append___rarg(x_17, x_20);
lean_dec(x_20);
x_22 = l_Array_append___rarg(x_21, x_3);
x_23 = lean_box(0);
x_24 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_11);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_25);
x_27 = l_Lake_proc(x_26, x_25, x_9, x_12);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_compileExe(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_array_mk(x_10);
x_12 = l_Array_append___rarg(x_5, x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Lake_download___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-f", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-S", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-s", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_download___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("curl", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_download___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_download___lambda__1___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_compileLeanModule___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lake_download___lambda__1___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lake_download___lambda__1___closed__3;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lake_download___lambda__1___closed__4;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_mk(x_19);
x_21 = lean_array_get_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
x_24 = lean_box(0);
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_21);
x_25 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_26 = l_Lake_download___lambda__1___closed__5;
x_27 = l_Lake_compileO___closed__1;
x_28 = 0;
x_29 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_20);
lean_ctor_set(x_29, 3, x_24);
lean_ctor_set(x_29, 4, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_28);
x_30 = 1;
x_31 = l_Lake_proc(x_29, x_30, x_5, x_6);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_21, x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_21);
x_33 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_34 = l_Lake_download___lambda__1___closed__5;
x_35 = l_Lake_compileO___closed__1;
x_36 = 0;
x_37 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_37, 2, x_20);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_36);
x_38 = 1;
x_39 = l_Lake_proc(x_37, x_38, x_5, x_6);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(x_7, x_3, x_40, x_41, x_20);
x_43 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_44 = l_Lake_download___lambda__1___closed__5;
x_45 = l_Lake_compileO___closed__1;
x_46 = 0;
x_47 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_42);
lean_ctor_set(x_47, 3, x_24);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*5, x_46);
x_48 = 1;
x_49 = l_Lake_proc(x_47, x_48, x_5, x_6);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_System_FilePath_pathExists(x_2, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = l_Lake_createParentDirs(x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_download___lambda__1(x_1, x_2, x_3, x_13, x_4, x_14);
lean_dec(x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_io_error_to_string(x_17);
x_19 = 3;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
x_21 = lean_array_get_size(x_4);
x_22 = lean_array_push(x_4, x_20);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_22);
lean_ctor_set(x_6, 0, x_21);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_io_error_to_string(x_23);
x_26 = 3;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_array_get_size(x_4);
x_29 = lean_array_push(x_4, x_27);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = l_Lake_createParentDirs(x_2, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lake_download___lambda__1(x_1, x_2, x_3, x_33, x_4, x_34);
lean_dec(x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_38 = x_32;
} else {
 lean_dec_ref(x_32);
 x_38 = lean_box(0);
}
x_39 = lean_io_error_to_string(x_36);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_4);
x_43 = lean_array_push(x_4, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
 lean_ctor_set_tag(x_45, 0);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_6);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_6, 0);
lean_dec(x_48);
x_49 = lean_io_remove_file(x_2, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lake_download___lambda__1(x_1, x_2, x_3, x_50, x_4, x_51);
lean_dec(x_50);
return x_52;
}
else
{
uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_io_error_to_string(x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_4);
x_59 = lean_array_push(x_4, x_57);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_59);
lean_ctor_set(x_6, 0, x_58);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_6);
return x_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_62 = lean_io_error_to_string(x_60);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_4);
x_66 = lean_array_push(x_4, x_64);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_66);
lean_ctor_set(x_6, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_61);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_dec(x_6);
x_69 = lean_io_remove_file(x_2, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lake_download___lambda__1(x_1, x_2, x_3, x_70, x_4, x_71);
lean_dec(x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = lean_io_error_to_string(x_73);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_4);
x_80 = lean_array_push(x_4, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_75;
 lean_ctor_set_tag(x_82, 0);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_74);
return x_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_download___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_download___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_download(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_untar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-C", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_untar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tar", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_untar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lake_untar___lambda__1___closed__1;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lake_download___lambda__1___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
x_16 = lean_box(0);
x_17 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_18 = l_Lake_untar___lambda__1___closed__2;
x_19 = l_Lake_compileO___closed__1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_15);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set(x_21, 4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_20);
x_22 = 1;
x_23 = l_Lake_proc(x_21, x_22, x_5, x_6);
return x_23;
}
}
static lean_object* _init_l_Lake_untar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-xvv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_untar___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 122;
x_2 = l_Lake_untar___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_untar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_23; 
x_23 = l_IO_FS_createDirAll(x_2, x_5);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_23, 1, x_4);
x_6 = x_23;
x_7 = x_25;
goto block_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_4);
x_6 = x_28;
x_7 = x_27;
goto block_22;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
x_32 = lean_io_error_to_string(x_30);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_array_get_size(x_4);
x_36 = lean_array_push(x_4, x_34);
lean_ctor_set(x_23, 1, x_36);
lean_ctor_set(x_23, 0, x_35);
x_6 = x_23;
x_7 = x_31;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_io_error_to_string(x_37);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_4);
x_43 = lean_array_push(x_4, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_6 = x_44;
x_7 = x_38;
goto block_22;
}
}
block_22:
{
if (lean_obj_tag(x_6) == 0)
{
if (x_3 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lake_untar___closed__1;
x_10 = lean_box(0);
x_11 = l_Lake_untar___lambda__1(x_2, x_1, x_9, x_10, x_8, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_Lake_untar___closed__2;
x_14 = lean_box(0);
x_15 = l_Lake_untar___lambda__1(x_2, x_1, x_13, x_14, x_12, x_7);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_untar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_untar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_untar(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exclude=", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_12 = lean_array_uget(x_3, x_5);
x_13 = l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_array_push(x_6, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_17;
goto _start;
}
}
}
static lean_object* _init_l_Lake_tar___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_tar___lambda__1___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_tar___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("COPYFILE_DISABLE", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___lambda__1___closed__4;
x_2 = l_Lake_tar___lambda__1___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_tar___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_1);
x_11 = 0;
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1(x_1, x_9, x_1, x_10, x_11, x_5, x_7, x_8);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Lake_tar___lambda__1___closed__1;
lean_inc(x_2);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_19);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_14);
lean_ctor_set(x_12, 0, x_3);
x_20 = l_Lake_untar___lambda__1___closed__1;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_download___lambda__1___closed__2;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_array_mk(x_24);
x_26 = l_Array_append___rarg(x_17, x_25);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_System_Platform_isOSX;
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_29 = lean_array_mk(x_2);
x_30 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_31 = l_Lake_untar___lambda__1___closed__2;
x_32 = 0;
x_33 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_26);
lean_ctor_set(x_33, 3, x_27);
lean_ctor_set(x_33, 4, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*5, x_32);
x_34 = 1;
x_35 = l_Lake_proc(x_33, x_34, x_18, x_16);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_36 = l_Lake_tar___lambda__1___closed__5;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_38 = lean_array_mk(x_37);
x_39 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_40 = l_Lake_untar___lambda__1___closed__2;
x_41 = 0;
x_42 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_26);
lean_ctor_set(x_42, 3, x_27);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_41);
x_43 = 1;
x_44 = l_Lake_proc(x_42, x_43, x_18, x_16);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_45 = lean_ctor_get(x_12, 1);
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = l_Lake_tar___lambda__1___closed__1;
lean_inc(x_2);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 1, x_49);
lean_ctor_set(x_12, 0, x_3);
x_50 = l_Lake_untar___lambda__1___closed__1;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_12);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lake_download___lambda__1___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_mk(x_54);
x_56 = l_Array_append___rarg(x_46, x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l_System_Platform_isOSX;
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_59 = lean_array_mk(x_2);
x_60 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_61 = l_Lake_untar___lambda__1___closed__2;
x_62 = 0;
x_63 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_56);
lean_ctor_set(x_63, 3, x_57);
lean_ctor_set(x_63, 4, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*5, x_62);
x_64 = 1;
x_65 = l_Lake_proc(x_63, x_64, x_47, x_45);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_66 = l_Lake_tar___lambda__1___closed__5;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_2);
x_68 = lean_array_mk(x_67);
x_69 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_70 = l_Lake_untar___lambda__1___closed__2;
x_71 = 0;
x_72 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_56);
lean_ctor_set(x_72, 3, x_57);
lean_ctor_set(x_72, 4, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_71);
x_73 = 1;
x_74 = l_Lake_proc(x_72, x_73, x_47, x_45);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_75 = lean_ctor_get(x_12, 0);
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_12);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_79 = x_75;
} else {
 lean_dec_ref(x_75);
 x_79 = lean_box(0);
}
x_80 = l_Lake_tar___lambda__1___closed__1;
lean_inc(x_2);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_79;
 lean_ctor_set_tag(x_81, 1);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_2);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lake_untar___lambda__1___closed__1;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_4);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lake_download___lambda__1___closed__2;
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
x_88 = lean_array_mk(x_87);
x_89 = l_Array_append___rarg(x_77, x_88);
lean_dec(x_88);
x_90 = lean_box(0);
x_91 = l_System_Platform_isOSX;
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_92 = lean_array_mk(x_2);
x_93 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_94 = l_Lake_untar___lambda__1___closed__2;
x_95 = 0;
x_96 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
lean_ctor_set(x_96, 2, x_89);
lean_ctor_set(x_96, 3, x_90);
lean_ctor_set(x_96, 4, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*5, x_95);
x_97 = 1;
x_98 = l_Lake_proc(x_96, x_97, x_78, x_76);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; 
x_99 = l_Lake_tar___lambda__1___closed__5;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
x_101 = lean_array_mk(x_100);
x_102 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_103 = l_Lake_untar___lambda__1___closed__2;
x_104 = 0;
x_105 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
lean_ctor_set(x_105, 2, x_89);
lean_ctor_set(x_105, 3, x_90);
lean_ctor_set(x_105, 4, x_101);
lean_ctor_set_uint8(x_105, sizeof(void*)*5, x_104);
x_106 = 1;
x_107 = l_Lake_proc(x_105, x_106, x_78, x_76);
return x_107;
}
}
}
}
static lean_object* _init_l_Lake_tar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-cvv", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_tar___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_tar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_tar___closed__2;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_tar___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-z", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_tar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_tar___closed__3;
x_2 = l_Lake_tar___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_24; 
x_24 = l_Lake_createParentDirs(x_2, x_6);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 1);
lean_ctor_set(x_24, 1, x_5);
x_7 = x_24;
x_8 = x_26;
goto block_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_5);
x_7 = x_29;
x_8 = x_28;
goto block_23;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
x_33 = lean_io_error_to_string(x_31);
x_34 = 3;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_array_get_size(x_5);
x_37 = lean_array_push(x_5, x_35);
lean_ctor_set(x_24, 1, x_37);
lean_ctor_set(x_24, 0, x_36);
x_7 = x_24;
x_8 = x_32;
goto block_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_io_error_to_string(x_38);
x_41 = 3;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_41);
x_43 = lean_array_get_size(x_5);
x_44 = lean_array_push(x_5, x_42);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_7 = x_45;
x_8 = x_39;
goto block_23;
}
}
block_23:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
if (x_3 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lake_tar___closed__3;
x_12 = lean_box(0);
x_13 = l_Lake_tar___lambda__1(x_4, x_10, x_1, x_2, x_11, x_12, x_9, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lake_tar___closed__5;
x_15 = lean_box(0);
x_16 = l_Lake_tar___lambda__1(x_4, x_10, x_1, x_2, x_14, x_15, x_9, x_8);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_tar___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_tar___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_tar(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_4);
return x_8;
}
}
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Proc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_NativeLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1);
l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1 = _init_l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1();
lean_mark_persistent(l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__1);
l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2 = _init_l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2();
lean_mark_persistent(l_Lake_logSerialMessage___at_Lake_compileLeanModule___spec__3___closed__2);
l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__1);
l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__2);
l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__4___closed__3);
l_Lake_compileLeanModule___lambda__1___closed__1 = _init_l_Lake_compileLeanModule___lambda__1___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__1___closed__1);
l_Lake_compileLeanModule___lambda__2___closed__1 = _init_l_Lake_compileLeanModule___lambda__2___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__2___closed__1);
l_Lake_compileLeanModule___lambda__3___closed__1 = _init_l_Lake_compileLeanModule___lambda__3___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__3___closed__1);
l_Lake_compileLeanModule___lambda__3___closed__2 = _init_l_Lake_compileLeanModule___lambda__3___closed__2();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__3___closed__2);
l_Lake_compileLeanModule___lambda__4___closed__1 = _init_l_Lake_compileLeanModule___lambda__4___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__4___closed__1);
l_Lake_compileLeanModule___lambda__4___closed__2 = _init_l_Lake_compileLeanModule___lambda__4___closed__2();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__4___closed__2);
l_Lake_compileLeanModule___lambda__4___closed__3 = _init_l_Lake_compileLeanModule___lambda__4___closed__3();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__4___closed__3);
l_Lake_compileLeanModule___lambda__5___closed__1 = _init_l_Lake_compileLeanModule___lambda__5___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__5___closed__1);
l_Lake_compileLeanModule___lambda__6___closed__1 = _init_l_Lake_compileLeanModule___lambda__6___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__6___closed__1);
l_Lake_compileLeanModule___lambda__7___closed__1 = _init_l_Lake_compileLeanModule___lambda__7___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___lambda__7___closed__1);
l_Lake_compileLeanModule___closed__1 = _init_l_Lake_compileLeanModule___closed__1();
lean_mark_persistent(l_Lake_compileLeanModule___closed__1);
l_Lake_compileLeanModule___closed__2 = _init_l_Lake_compileLeanModule___closed__2();
lean_mark_persistent(l_Lake_compileLeanModule___closed__2);
l_Lake_compileO___closed__1 = _init_l_Lake_compileO___closed__1();
lean_mark_persistent(l_Lake_compileO___closed__1);
l_Lake_compileStaticLib___closed__1 = _init_l_Lake_compileStaticLib___closed__1();
lean_mark_persistent(l_Lake_compileStaticLib___closed__1);
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
l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6 = _init_l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6();
lean_mark_persistent(l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6);
l_Lake_compileSharedLib___closed__1 = _init_l_Lake_compileSharedLib___closed__1();
lean_mark_persistent(l_Lake_compileSharedLib___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1);
l_Lake_download___lambda__1___closed__1 = _init_l_Lake_download___lambda__1___closed__1();
lean_mark_persistent(l_Lake_download___lambda__1___closed__1);
l_Lake_download___lambda__1___closed__2 = _init_l_Lake_download___lambda__1___closed__2();
lean_mark_persistent(l_Lake_download___lambda__1___closed__2);
l_Lake_download___lambda__1___closed__3 = _init_l_Lake_download___lambda__1___closed__3();
lean_mark_persistent(l_Lake_download___lambda__1___closed__3);
l_Lake_download___lambda__1___closed__4 = _init_l_Lake_download___lambda__1___closed__4();
lean_mark_persistent(l_Lake_download___lambda__1___closed__4);
l_Lake_download___lambda__1___closed__5 = _init_l_Lake_download___lambda__1___closed__5();
lean_mark_persistent(l_Lake_download___lambda__1___closed__5);
l_Lake_untar___lambda__1___closed__1 = _init_l_Lake_untar___lambda__1___closed__1();
lean_mark_persistent(l_Lake_untar___lambda__1___closed__1);
l_Lake_untar___lambda__1___closed__2 = _init_l_Lake_untar___lambda__1___closed__2();
lean_mark_persistent(l_Lake_untar___lambda__1___closed__2);
l_Lake_untar___closed__1 = _init_l_Lake_untar___closed__1();
lean_mark_persistent(l_Lake_untar___closed__1);
l_Lake_untar___closed__2 = _init_l_Lake_untar___closed__2();
lean_mark_persistent(l_Lake_untar___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___closed__1);
l_Lake_tar___lambda__1___closed__1 = _init_l_Lake_tar___lambda__1___closed__1();
lean_mark_persistent(l_Lake_tar___lambda__1___closed__1);
l_Lake_tar___lambda__1___closed__2 = _init_l_Lake_tar___lambda__1___closed__2();
lean_mark_persistent(l_Lake_tar___lambda__1___closed__2);
l_Lake_tar___lambda__1___closed__3 = _init_l_Lake_tar___lambda__1___closed__3();
lean_mark_persistent(l_Lake_tar___lambda__1___closed__3);
l_Lake_tar___lambda__1___closed__4 = _init_l_Lake_tar___lambda__1___closed__4();
lean_mark_persistent(l_Lake_tar___lambda__1___closed__4);
l_Lake_tar___lambda__1___closed__5 = _init_l_Lake_tar___lambda__1___closed__5();
lean_mark_persistent(l_Lake_tar___lambda__1___closed__5);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
