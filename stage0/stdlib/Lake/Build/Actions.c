// Lean compiler output
// Module: Lake.Build.Actions
// Imports: Lake.Config.Dynlib Lake.Util.Proc Lake.Util.NativeLib Lake.Util.IO
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__1;
static lean_object* l_Lake_tar___lambda__1___closed__5;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1;
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
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
static lean_object* l_Lake_download___lambda__1___closed__5;
static lean_object* l_Lake_compileLeanModule___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___lambda__1___closed__1;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1___closed__1;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_mkArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_download___lambda__1___closed__4;
static lean_object* l_Lake_tar___lambda__1___closed__3;
static lean_object* l_Lake_compileLeanModule___closed__2;
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* l_String_split___at_Lean_stringToMessageData___spec__1(lean_object*);
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__4;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_tar___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__6;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__5;
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_untar___lambda__1___closed__2;
static lean_object* l_Lake_compileStaticLib___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_untar___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1;
lean_object* l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3919_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lake_compileO___closed__1;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_mkArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_compileLeanModule___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
lean_object* l_Lean_Json_Parser_any(lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_mkArgs___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_tar___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2;
static lean_object* l_Lake_mkArgs___closed__1;
static lean_object* l_Lake_tar___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__7___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__4___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_compileStaticLib___closed__2;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___lambda__2___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_untar___closed__1;
static lean_object* l_Lake_tar___lambda__1___closed__4;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_13 = lean_array_uget(x_4, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__1___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_mk(x_17);
x_19 = l_Array_append___rarg(x_7, x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
x_7 = x_19;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_13 = lean_array_uget(x_4, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2___closed__1;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_mk(x_17);
x_19 = l_Array_append___rarg(x_7, x_18);
lean_dec(x_18);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
x_7 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 2);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lake_LogEntry_ofSerialMessage(x_1);
x_9 = lean_array_push(x_4, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_25 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2;
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
x_29 = l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_3919_(x_28);
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
x_34 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3;
x_35 = lean_string_append(x_34, x_2);
x_36 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_37 = lean_string_append(x_35, x_36);
x_38 = 1;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_push(x_4, x_39);
x_41 = lean_box(0);
x_42 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1(x_31, x_2, x_41, x_40, x_5);
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
x_49 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1(x_31, x_2, x_48, x_4, x_5);
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
x_14 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1;
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
x_20 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1;
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
x_16 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
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
x_14 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
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
x_19 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
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
x_34 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
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
x_35 = 1;
x_36 = 0;
lean_inc(x_5);
x_37 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_28);
lean_ctor_set(x_37, 3, x_29);
lean_ctor_set(x_37, 4, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 1, x_36);
x_38 = lean_array_get_size(x_26);
lean_inc(x_37);
x_123 = l_Lake_mkCmdLog(x_37);
x_124 = 0;
x_125 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*1, x_124);
x_126 = lean_array_push(x_26, x_125);
x_127 = lean_box(0);
x_128 = l_Lake_compileLeanModule___lambda__3(x_37, x_5, x_127, x_126, x_22);
lean_dec(x_5);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_39 = x_129;
x_40 = x_130;
goto block_122;
}
else
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = !lean_is_exclusive(x_129);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_129, 0);
lean_dec(x_133);
lean_inc(x_38);
lean_ctor_set(x_129, 0, x_38);
x_39 = x_129;
x_40 = x_131;
goto block_122;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
lean_dec(x_129);
lean_inc(x_38);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_38);
lean_ctor_set(x_135, 1, x_134);
x_39 = x_135;
x_40 = x_131;
goto block_122;
}
}
block_122:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_23);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_string_utf8_byte_size(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = l_String_split___at_Lean_stringToMessageData___spec__1(x_43);
lean_dec(x_43);
x_48 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_49 = l_List_foldlM___at_Lake_compileLeanModule___spec__3(x_45, x_48, x_47, x_42, x_40);
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
x_54 = lean_string_utf8_byte_size(x_52);
x_55 = lean_nat_dec_eq(x_54, x_45);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3;
x_57 = lean_string_append(x_56, x_52);
lean_dec(x_52);
x_58 = lean_string_append(x_57, x_48);
x_59 = 1;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_push(x_53, x_60);
x_62 = lean_box(0);
x_63 = l_Lake_compileLeanModule___lambda__2(x_41, x_62, x_61, x_51);
lean_dec(x_41);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
lean_dec(x_38);
x_65 = !lean_is_exclusive(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_63);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_63, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_64);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_64, 0);
lean_dec(x_72);
lean_ctor_set(x_64, 0, x_38);
return x_63;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_64, 1);
lean_inc(x_73);
lean_dec(x_64);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_38);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_63, 0, x_74);
return x_63;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_dec(x_63);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_77 = x_64;
} else {
 lean_dec_ref(x_64);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_38);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_52);
x_80 = lean_box(0);
x_81 = l_Lake_compileLeanModule___lambda__2(x_41, x_80, x_53, x_51);
lean_dec(x_41);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
lean_dec(x_38);
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 0);
lean_dec(x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_81);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_81, 0);
lean_dec(x_88);
x_89 = !lean_is_exclusive(x_82);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_82, 0);
lean_dec(x_90);
lean_ctor_set(x_82, 0, x_38);
return x_81;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_38);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_81, 0, x_92);
return x_81;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_dec(x_81);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_38);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_93);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_43);
x_98 = lean_box(0);
x_99 = l_Lake_compileLeanModule___lambda__2(x_41, x_98, x_42, x_40);
lean_dec(x_41);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
lean_dec(x_38);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_100);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_99, 0);
lean_dec(x_106);
x_107 = !lean_is_exclusive(x_100);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_100, 0);
lean_dec(x_108);
lean_ctor_set(x_100, 0, x_38);
return x_99;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_38);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set(x_99, 0, x_110);
return x_99;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_99, 1);
lean_inc(x_111);
lean_dec(x_99);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_113 = x_100;
} else {
 lean_dec_ref(x_100);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_38);
lean_ctor_set(x_114, 1, x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_39);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_39, 0);
lean_dec(x_117);
lean_ctor_set(x_39, 0, x_38);
if (lean_is_scalar(x_23)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_23;
}
lean_ctor_set(x_118, 0, x_39);
lean_ctor_set(x_118, 1, x_40);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_39, 1);
lean_inc(x_119);
lean_dec(x_39);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_38);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_23)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_23;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_40);
return x_121;
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_136 = lean_ctor_get(x_21, 0);
x_137 = lean_ctor_get(x_21, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_21);
x_138 = l_Lake_compileLeanModule___lambda__4___closed__1;
x_139 = lean_array_push(x_136, x_138);
x_140 = lean_box(0);
x_141 = l_System_SearchPath_toString(x_4);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lake_compileLeanModule___lambda__4___closed__3;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 0, x_144);
x_145 = lean_array_mk(x_14);
x_146 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_147 = 1;
x_148 = 0;
lean_inc(x_5);
x_149 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_5);
lean_ctor_set(x_149, 2, x_139);
lean_ctor_set(x_149, 3, x_140);
lean_ctor_set(x_149, 4, x_145);
lean_ctor_set_uint8(x_149, sizeof(void*)*5, x_147);
lean_ctor_set_uint8(x_149, sizeof(void*)*5 + 1, x_148);
x_150 = lean_array_get_size(x_137);
lean_inc(x_149);
x_215 = l_Lake_mkCmdLog(x_149);
x_216 = 0;
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_216);
x_218 = lean_array_push(x_137, x_217);
x_219 = lean_box(0);
x_220 = l_Lake_compileLeanModule___lambda__3(x_149, x_5, x_219, x_218, x_22);
lean_dec(x_5);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_151 = x_221;
x_152 = x_222;
goto block_214;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_225 = x_221;
} else {
 lean_dec_ref(x_221);
 x_225 = lean_box(0);
}
lean_inc(x_150);
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_150);
lean_ctor_set(x_226, 1, x_224);
x_151 = x_226;
x_152 = x_223;
goto block_214;
}
block_214:
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
lean_dec(x_23);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
x_156 = lean_string_utf8_byte_size(x_155);
x_157 = lean_unsigned_to_nat(0u);
x_158 = lean_nat_dec_eq(x_156, x_157);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_159 = l_String_split___at_Lean_stringToMessageData___spec__1(x_155);
lean_dec(x_155);
x_160 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_161 = l_List_foldlM___at_Lake_compileLeanModule___spec__3(x_157, x_160, x_159, x_154, x_152);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_string_utf8_byte_size(x_164);
x_167 = lean_nat_dec_eq(x_166, x_157);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_168 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3;
x_169 = lean_string_append(x_168, x_164);
lean_dec(x_164);
x_170 = lean_string_append(x_169, x_160);
x_171 = 1;
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_171);
x_173 = lean_array_push(x_165, x_172);
x_174 = lean_box(0);
x_175 = l_Lake_compileLeanModule___lambda__2(x_153, x_174, x_173, x_163);
lean_dec(x_153);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_150);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_181 = x_175;
} else {
 lean_dec_ref(x_175);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_150);
lean_ctor_set(x_184, 1, x_182);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_181;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_180);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_164);
x_186 = lean_box(0);
x_187 = l_Lake_compileLeanModule___lambda__2(x_153, x_186, x_165, x_163);
lean_dec(x_153);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_150);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_193 = x_187;
} else {
 lean_dec_ref(x_187);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_195 = x_188;
} else {
 lean_dec_ref(x_188);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_150);
lean_ctor_set(x_196, 1, x_194);
if (lean_is_scalar(x_193)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_193;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_192);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
x_198 = lean_box(0);
x_199 = l_Lake_compileLeanModule___lambda__2(x_153, x_198, x_154, x_152);
lean_dec(x_153);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_150);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_199, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_205 = x_199;
} else {
 lean_dec_ref(x_199);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_200, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_207 = x_200;
} else {
 lean_dec_ref(x_200);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_150);
lean_ctor_set(x_208, 1, x_206);
if (lean_is_scalar(x_205)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_205;
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_204);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_151, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_211 = x_151;
} else {
 lean_dec_ref(x_151);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_150);
lean_ctor_set(x_212, 1, x_210);
if (lean_is_scalar(x_23)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_23;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_152);
return x_213;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; size_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_227 = lean_ctor_get(x_14, 0);
x_228 = lean_ctor_get(x_14, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_14);
x_229 = lean_array_size(x_3);
lean_inc(x_2);
x_230 = l_Array_forIn_x27Unsafe_loop___at_Lake_compileLeanModule___spec__2(x_3, x_2, x_10, x_3, x_229, x_12, x_227, x_228, x_15);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_231, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_236 = x_231;
} else {
 lean_dec_ref(x_231);
 x_236 = lean_box(0);
}
x_237 = l_Lake_compileLeanModule___lambda__4___closed__1;
x_238 = lean_array_push(x_234, x_237);
x_239 = lean_box(0);
x_240 = l_System_SearchPath_toString(x_4);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l_Lake_compileLeanModule___lambda__4___closed__3;
if (lean_is_scalar(x_236)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_236;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_2);
x_245 = lean_array_mk(x_244);
x_246 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_247 = 1;
x_248 = 0;
lean_inc(x_5);
x_249 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_5);
lean_ctor_set(x_249, 2, x_238);
lean_ctor_set(x_249, 3, x_239);
lean_ctor_set(x_249, 4, x_245);
lean_ctor_set_uint8(x_249, sizeof(void*)*5, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*5 + 1, x_248);
x_250 = lean_array_get_size(x_235);
lean_inc(x_249);
x_315 = l_Lake_mkCmdLog(x_249);
x_316 = 0;
x_317 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*1, x_316);
x_318 = lean_array_push(x_235, x_317);
x_319 = lean_box(0);
x_320 = l_Lake_compileLeanModule___lambda__3(x_249, x_5, x_319, x_318, x_232);
lean_dec(x_5);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_251 = x_321;
x_252 = x_322;
goto block_314;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_325 = x_321;
} else {
 lean_dec_ref(x_321);
 x_325 = lean_box(0);
}
lean_inc(x_250);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 2, 0);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_250);
lean_ctor_set(x_326, 1, x_324);
x_251 = x_326;
x_252 = x_323;
goto block_314;
}
block_314:
{
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_dec(x_233);
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
x_255 = lean_ctor_get(x_253, 0);
lean_inc(x_255);
x_256 = lean_string_utf8_byte_size(x_255);
x_257 = lean_unsigned_to_nat(0u);
x_258 = lean_nat_dec_eq(x_256, x_257);
lean_dec(x_256);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_259 = l_String_split___at_Lean_stringToMessageData___spec__1(x_255);
lean_dec(x_255);
x_260 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_261 = l_List_foldlM___at_Lake_compileLeanModule___spec__3(x_257, x_260, x_259, x_254, x_252);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_262, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = lean_string_utf8_byte_size(x_264);
x_267 = lean_nat_dec_eq(x_266, x_257);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_268 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3;
x_269 = lean_string_append(x_268, x_264);
lean_dec(x_264);
x_270 = lean_string_append(x_269, x_260);
x_271 = 1;
x_272 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_271);
x_273 = lean_array_push(x_265, x_272);
x_274 = lean_box(0);
x_275 = l_Lake_compileLeanModule___lambda__2(x_253, x_274, x_273, x_263);
lean_dec(x_253);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_250);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_280 = lean_ctor_get(x_275, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
 x_281 = lean_box(0);
}
x_282 = lean_ctor_get(x_276, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_283 = x_276;
} else {
 lean_dec_ref(x_276);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_250);
lean_ctor_set(x_284, 1, x_282);
if (lean_is_scalar(x_281)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_281;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_280);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_264);
x_286 = lean_box(0);
x_287 = l_Lake_compileLeanModule___lambda__2(x_253, x_286, x_265, x_263);
lean_dec(x_253);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_250);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_287, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_293 = x_287;
} else {
 lean_dec_ref(x_287);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_288, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_295 = x_288;
} else {
 lean_dec_ref(x_288);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_250);
lean_ctor_set(x_296, 1, x_294);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_292);
return x_297;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_255);
x_298 = lean_box(0);
x_299 = l_Lake_compileLeanModule___lambda__2(x_253, x_298, x_254, x_252);
lean_dec(x_253);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_250);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_304 = lean_ctor_get(x_299, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_305 = x_299;
} else {
 lean_dec_ref(x_299);
 x_305 = lean_box(0);
}
x_306 = lean_ctor_get(x_300, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_307 = x_300;
} else {
 lean_dec_ref(x_300);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_250);
lean_ctor_set(x_308, 1, x_306);
if (lean_is_scalar(x_305)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_305;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_304);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_251, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_311 = x_251;
} else {
 lean_dec_ref(x_251);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_250);
lean_ctor_set(x_312, 1, x_310);
if (lean_is_scalar(x_233)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_233;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_252);
return x_313;
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
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lake_compileLeanModule___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___at_Lake_compileLeanModule___spec__3(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
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
x_21 = 1;
x_22 = 0;
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_22);
x_24 = l_Lake_proc(x_23, x_22, x_5, x_8);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = 3;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_30 = lean_array_get_size(x_5);
x_31 = lean_array_push(x_5, x_29);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_32);
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_io_error_to_string(x_33);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_array_get_size(x_5);
x_39 = lean_array_push(x_5, x_37);
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
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_compileO(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_mkArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = 92;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 34;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_string_push(x_4, x_7);
x_3 = x_6;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_string_push(x_4, x_8);
x_15 = lean_string_push(x_14, x_7);
x_3 = x_6;
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_string_push(x_4, x_8);
x_18 = lean_string_push(x_17, x_7);
x_3 = x_6;
x_4 = x_18;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_13 = l_String_foldlAux___at_Lake_mkArgs___spec__1(x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_io_prim_handle_put_str(x_1, x_17, x_7);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
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
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_18, 0);
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
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
x_34 = lean_io_error_to_string(x_32);
x_35 = 3;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_get_size(x_6);
x_38 = lean_array_push(x_6, x_36);
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
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_6);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
return x_42;
}
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
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_System_Platform_isWindows;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_39; lean_object* x_40; uint8_t x_79; lean_object* x_80; 
x_8 = l_Lake_mkArgs___closed__1;
x_9 = l_System_FilePath_addExtension(x_1, x_8);
x_79 = 1;
x_80 = lean_io_prim_handle_mk(x_9, x_79, x_4);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 1);
lean_ctor_set(x_80, 1, x_3);
x_39 = x_80;
x_40 = x_82;
goto block_78;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_80, 0);
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_80);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_3);
x_39 = x_85;
x_40 = x_84;
goto block_78;
}
}
else
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_80);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_80, 0);
x_88 = lean_ctor_get(x_80, 1);
x_89 = lean_io_error_to_string(x_87);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_3);
x_93 = lean_array_push(x_3, x_91);
lean_ctor_set(x_80, 1, x_93);
lean_ctor_set(x_80, 0, x_92);
x_39 = x_80;
x_40 = x_88;
goto block_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_80, 0);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_80);
x_96 = lean_io_error_to_string(x_94);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_3);
x_100 = lean_array_push(x_3, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_39 = x_101;
x_40 = x_95;
goto block_78;
}
}
block_38:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lake_mkArgs___closed__2;
x_15 = lean_string_append(x_14, x_9);
lean_dec(x_9);
x_16 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_mk(x_19);
lean_ctor_set(x_10, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lake_mkArgs___closed__2;
x_24 = lean_string_append(x_23, x_9);
lean_dec(x_9);
x_25 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_mk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_11);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_11);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
block_78:
{
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_39, 0);
x_43 = lean_ctor_get(x_39, 1);
x_44 = lean_array_get_size(x_2);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_lt(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_2);
x_47 = lean_box(0);
lean_ctor_set(x_39, 0, x_47);
x_10 = x_39;
x_11 = x_40;
goto block_38;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_44, x_44);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_2);
x_49 = lean_box(0);
lean_ctor_set(x_39, 0, x_49);
x_10 = x_39;
x_11 = x_40;
goto block_38;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_39);
x_50 = 0;
x_51 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_52 = lean_box(0);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2(x_42, x_2, x_50, x_51, x_52, x_43, x_40);
lean_dec(x_2);
lean_dec(x_42);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_10 = x_54;
x_11 = x_55;
goto block_38;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_array_get_size(x_2);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_lt(x_59, x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_2);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
x_10 = x_62;
x_11 = x_40;
goto block_38;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_58, x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
x_10 = x_65;
x_11 = x_40;
goto block_38;
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_68 = lean_box(0);
x_69 = l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2(x_56, x_2, x_66, x_67, x_68, x_57, x_40);
lean_dec(x_2);
lean_dec(x_56);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_10 = x_70;
x_11 = x_71;
goto block_38;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_9);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_39);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_39);
lean_ctor_set(x_73, 1, x_40);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_40);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at_Lake_mkArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at_Lake_mkArgs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
static lean_object* _init_l_Lake_compileStaticLib___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_compileStaticLib___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_compileStaticLib___closed__2;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--thin", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_compileStaticLib___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileStaticLib___closed__3;
x_2 = l_Lake_compileStaticLib___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_74; 
x_74 = l_Lake_createParentDirs(x_1, x_6);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 1);
lean_ctor_set(x_74, 1, x_5);
x_7 = x_74;
x_8 = x_76;
goto block_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_5);
x_7 = x_79;
x_8 = x_78;
goto block_73;
}
}
else
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_74);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_74, 0);
x_82 = lean_ctor_get(x_74, 1);
x_83 = lean_io_error_to_string(x_81);
x_84 = 3;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = lean_array_get_size(x_5);
x_87 = lean_array_push(x_5, x_85);
lean_ctor_set(x_74, 1, x_87);
lean_ctor_set(x_74, 0, x_86);
x_7 = x_74;
x_8 = x_82;
goto block_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_74, 0);
x_89 = lean_ctor_get(x_74, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_74);
x_90 = lean_io_error_to_string(x_88);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_array_get_size(x_5);
x_94 = lean_array_push(x_5, x_92);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_7 = x_95;
x_8 = x_89;
goto block_73;
}
}
block_73:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lake_compileStaticLib___spec__1(x_10, x_11, x_2);
if (x_4 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_13 = l_Lake_mkArgs(x_1, x_12, x_9, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lake_compileStaticLib___closed__3;
x_19 = lean_array_push(x_18, x_1);
x_20 = l_Array_append___rarg(x_19, x_16);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_23 = l_Lake_compileO___closed__1;
x_24 = 1;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_20);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set(x_26, 4, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_25);
x_27 = l_Lake_proc(x_26, x_25, x_17, x_15);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_13, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_13, 0, x_33);
return x_13;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_37 = x_14;
} else {
 lean_dec_ref(x_14);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_inc(x_1);
x_40 = l_Lake_mkArgs(x_1, x_12, x_9, x_8);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lake_compileStaticLib___closed__5;
x_46 = lean_array_push(x_45, x_1);
x_47 = l_Array_append___rarg(x_46, x_43);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_50 = l_Lake_compileO___closed__1;
x_51 = 1;
x_52 = 0;
x_53 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 1, x_52);
x_54 = l_Lake_proc(x_53, x_52, x_44, x_42);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_40, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
return x_40;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_41, 0);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_41);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_40, 0, x_60);
return x_40;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_dec(x_40);
x_62 = lean_ctor_get(x_41, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_64 = x_41;
} else {
 lean_dec_ref(x_41);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_7);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_7);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_7, 0);
x_70 = lean_ctor_get(x_7, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_7);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_8);
return x_72;
}
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
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lake_compileStaticLib(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
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
lean_object* x_6; lean_object* x_7; lean_object* x_54; 
x_54 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 1);
lean_ctor_set(x_54, 1, x_4);
x_6 = x_54;
x_7 = x_56;
goto block_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_54);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_4);
x_6 = x_59;
x_7 = x_58;
goto block_53;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_54);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_54, 0);
x_62 = lean_ctor_get(x_54, 1);
x_63 = lean_io_error_to_string(x_61);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_4);
x_67 = lean_array_push(x_4, x_65);
lean_ctor_set(x_54, 1, x_67);
lean_ctor_set(x_54, 0, x_66);
x_6 = x_54;
x_7 = x_62;
goto block_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_54, 0);
x_69 = lean_ctor_get(x_54, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_54);
x_70 = lean_io_error_to_string(x_68);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_get_size(x_4);
x_74 = lean_array_push(x_4, x_72);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_6 = x_75;
x_7 = x_69;
goto block_53;
}
}
block_53:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lake_mkArgs(x_1, x_2, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_compileLeanModule___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lake_compileSharedLib___closed__1;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_mk(x_22);
x_24 = l_Array_append___rarg(x_23, x_12);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_27 = 1;
x_28 = 0;
x_29 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_15);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_28);
x_30 = l_Lake_proc(x_29, x_28, x_13, x_16);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_9, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_10, 0);
x_39 = lean_ctor_get(x_10, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_10);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_9, 0, x_40);
return x_9;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_dec(x_9);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_44 = x_10;
} else {
 lean_dec_ref(x_10);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_7);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_52; 
x_52 = l_Lake_createParentDirs(x_1, x_5);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 1);
lean_ctor_set(x_52, 1, x_4);
x_6 = x_52;
x_7 = x_54;
goto block_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_4);
x_6 = x_57;
x_7 = x_56;
goto block_51;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
x_61 = lean_io_error_to_string(x_59);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_4);
x_65 = lean_array_push(x_4, x_63);
lean_ctor_set(x_52, 1, x_65);
lean_ctor_set(x_52, 0, x_64);
x_6 = x_52;
x_7 = x_60;
goto block_51;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_52, 0);
x_67 = lean_ctor_get(x_52, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_52);
x_68 = lean_io_error_to_string(x_66);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_get_size(x_4);
x_72 = lean_array_push(x_4, x_70);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_6 = x_73;
x_7 = x_67;
goto block_51;
}
}
block_51:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lake_mkArgs(x_1, x_2, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_compileLeanModule___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_array_mk(x_20);
x_22 = l_Array_append___rarg(x_21, x_12);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_25 = 1;
x_26 = 0;
x_27 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_3);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_15);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*5 + 1, x_26);
x_28 = l_Lake_proc(x_27, x_26, x_13, x_16);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_9);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_9, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_9, 0, x_38);
return x_9;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_ctor_get(x_10, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_10, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_42 = x_10;
} else {
 lean_dec_ref(x_10);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_39);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_6);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_6, 0);
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_6);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_7);
return x_50;
}
}
}
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
x_25 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_26 = l_Lake_download___lambda__1___closed__5;
x_27 = l_Lake_compileO___closed__1;
x_28 = 1;
x_29 = 0;
x_30 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_24);
lean_ctor_set(x_30, 4, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*5, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*5 + 1, x_29);
x_31 = l_Lake_proc(x_30, x_28, x_5, x_6);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_21, x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_21);
x_33 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_34 = l_Lake_download___lambda__1___closed__5;
x_35 = l_Lake_compileO___closed__1;
x_36 = 1;
x_37 = 0;
x_38 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_20);
lean_ctor_set(x_38, 3, x_24);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*5, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*5 + 1, x_37);
x_39 = l_Lake_proc(x_38, x_36, x_5, x_6);
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_download___spec__1(x_7, x_3, x_40, x_41, x_20);
x_43 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_44 = l_Lake_download___lambda__1___closed__5;
x_45 = l_Lake_compileO___closed__1;
x_46 = 1;
x_47 = 0;
x_48 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_24);
lean_ctor_set(x_48, 4, x_45);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_47);
x_49 = l_Lake_proc(x_48, x_46, x_5, x_6);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
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
x_20 = 1;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_15);
lean_ctor_set(x_22, 3, x_16);
lean_ctor_set(x_22, 4, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*5 + 1, x_21);
x_23 = l_Lake_proc(x_22, x_20, x_5, x_6);
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
x_15 = l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4;
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_array_mk(x_2);
x_30 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_31 = l_Lake_untar___lambda__1___closed__2;
x_32 = 1;
x_33 = 0;
x_34 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_26);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 1, x_33);
x_35 = l_Lake_proc(x_34, x_32, x_18, x_16);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_36 = l_Lake_tar___lambda__1___closed__5;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_38 = lean_array_mk(x_37);
x_39 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_40 = l_Lake_untar___lambda__1___closed__2;
x_41 = 1;
x_42 = 0;
x_43 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_26);
lean_ctor_set(x_43, 3, x_27);
lean_ctor_set(x_43, 4, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_42);
x_44 = l_Lake_proc(x_43, x_41, x_18, x_16);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_array_mk(x_2);
x_60 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_61 = l_Lake_untar___lambda__1___closed__2;
x_62 = 1;
x_63 = 0;
x_64 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_59);
lean_ctor_set_uint8(x_64, sizeof(void*)*5, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*5 + 1, x_63);
x_65 = l_Lake_proc(x_64, x_62, x_47, x_45);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; 
x_66 = l_Lake_tar___lambda__1___closed__5;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_2);
x_68 = lean_array_mk(x_67);
x_69 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_70 = l_Lake_untar___lambda__1___closed__2;
x_71 = 1;
x_72 = 0;
x_73 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_56);
lean_ctor_set(x_73, 3, x_57);
lean_ctor_set(x_73, 4, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*5, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*5 + 1, x_72);
x_74 = l_Lake_proc(x_73, x_71, x_47, x_45);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_array_mk(x_2);
x_93 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_94 = l_Lake_untar___lambda__1___closed__2;
x_95 = 1;
x_96 = 0;
x_97 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_94);
lean_ctor_set(x_97, 2, x_89);
lean_ctor_set(x_97, 3, x_90);
lean_ctor_set(x_97, 4, x_92);
lean_ctor_set_uint8(x_97, sizeof(void*)*5, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*5 + 1, x_96);
x_98 = l_Lake_proc(x_97, x_95, x_78, x_76);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_99 = l_Lake_tar___lambda__1___closed__5;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_2);
x_101 = lean_array_mk(x_100);
x_102 = l_Lake_compileLeanModule___lambda__4___closed__2;
x_103 = l_Lake_untar___lambda__1___closed__2;
x_104 = 1;
x_105 = 0;
x_106 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_103);
lean_ctor_set(x_106, 2, x_89);
lean_ctor_set(x_106, 3, x_90);
lean_ctor_set(x_106, 4, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*5, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*5 + 1, x_105);
x_107 = l_Lake_proc(x_106, x_104, x_78, x_76);
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
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_NativeLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Dynlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__1);
l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__2);
l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__3);
l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4 = _init_l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4();
lean_mark_persistent(l_List_foldlM___at_Lake_compileLeanModule___spec__3___closed__4);
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
l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_mkArgs___spec__2___closed__2);
l_Lake_mkArgs___closed__1 = _init_l_Lake_mkArgs___closed__1();
lean_mark_persistent(l_Lake_mkArgs___closed__1);
l_Lake_mkArgs___closed__2 = _init_l_Lake_mkArgs___closed__2();
lean_mark_persistent(l_Lake_mkArgs___closed__2);
l_Lake_compileStaticLib___closed__1 = _init_l_Lake_compileStaticLib___closed__1();
lean_mark_persistent(l_Lake_compileStaticLib___closed__1);
l_Lake_compileStaticLib___closed__2 = _init_l_Lake_compileStaticLib___closed__2();
lean_mark_persistent(l_Lake_compileStaticLib___closed__2);
l_Lake_compileStaticLib___closed__3 = _init_l_Lake_compileStaticLib___closed__3();
lean_mark_persistent(l_Lake_compileStaticLib___closed__3);
l_Lake_compileStaticLib___closed__4 = _init_l_Lake_compileStaticLib___closed__4();
lean_mark_persistent(l_Lake_compileStaticLib___closed__4);
l_Lake_compileStaticLib___closed__5 = _init_l_Lake_compileStaticLib___closed__5();
lean_mark_persistent(l_Lake_compileStaticLib___closed__5);
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
