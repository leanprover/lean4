// Lean compiler output
// Module: Lake.Build.Actions
// Imports: Lean.Setup Lean.Data.Json Lake.Config.Dynlib Lake.Util.Proc Lake.Util.NativeLib Lake.Util.FilePath Lake.Util.IO
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
LEAN_EXPORT lean_object* l_Lake_compileO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__8;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__9;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__5;
static lean_object* l_Lake_compileLeanModule___closed__6;
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__13;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileSharedLib(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_4128_(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__10;
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_String_split___at___Lean_stringToMessageData_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__5;
LEAN_EXPORT lean_object* l_Lake_compileExe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l_Lake_untar___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__17;
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__11;
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0;
lean_object* l_Lake_createParentDirs(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__4;
static lean_object* l_Lake_download___closed__3;
LEAN_EXPORT lean_object* l_Lake_compileStaticLib___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileSharedLib___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__7;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__0;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
static lean_object* l_Lake_tar___closed__8;
LEAN_EXPORT lean_object* l_Lake_download___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1598_(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkArgs(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__9;
static lean_object* l_Lake_compileLeanModule___closed__0;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__0;
lean_object* l_IO_Process_output(lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__2;
LEAN_EXPORT lean_object* l_Lake_untar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__3;
static lean_object* l_Lake_compileSharedLib___closed__0;
static lean_object* l_Lake_compileLeanModule___closed__15;
static lean_object* l_Lake_download___closed__4;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__16;
static lean_object* l_Lake_untar___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mkArgs___closed__0;
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_untar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_compileO___closed__0;
static lean_object* l_Lake_untar___closed__4;
LEAN_EXPORT lean_object* l_Lake_compileLeanModule___lam__0(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
LEAN_EXPORT lean_object* l_Lake_compileO___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileStaticLib___closed__1;
static lean_object* l_Lake_compileStaticLib___closed__0;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_mkArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__5;
static lean_object* l_Lake_tar___closed__6;
static lean_object* l_Lake_compileO___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_System_SearchPath_toString(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_tar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__14;
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_tar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_download___closed__7;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__4;
static lean_object* l_Lake_compileLeanModule___closed__12;
lean_object* l_Lake_mkRelPathString(lean_object*);
static lean_object* l_Lake_compileO___closed__2;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1;
static lean_object* l_Lake_compileLeanModule___closed__3;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__19;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lake_mkArgs___closed__2;
static lean_object* l_Lake_compileLeanModule___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__8;
static lean_object* l_Lake_mkArgs___closed__1;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_tar___closed__3;
static lean_object* l_Lake_download___closed__6;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__18;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_compileStaticLib___closed__2;
static lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lake_LogEntry_ofSerialMessage(lean_object*);
static lean_object* l_Lake_download___closed__2;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
static lean_object* l_Lake_compileLeanModule___closed__10;
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__1;
static lean_object* l_Lake_tar___closed__7;
static lean_object* l_Lake_untar___closed__1;
static lean_object* l_Lake_compileO___closed__3;
static lean_object* l_Lake_untar___closed__3;
static lean_object* l_Lake_tar___closed__9;
static lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__3;
static lean_object* l_Lake_compileLeanModule___lam__0___closed__1;
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdout:\n", 8, 8);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lake_compileLeanModule_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
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
lean_dec(x_3);
lean_inc(x_8);
x_22 = l_Lean_Json_parse(x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_22);
goto block_21;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Message_0__Lean_fromJsonSerialMessage____x40_Lean_Message___hyg_4128_(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_24);
goto block_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_65 = lean_string_utf8_byte_size(x_2);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1;
x_69 = lean_string_append(x_68, x_2);
x_70 = lean_box(1);
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = lean_array_push(x_4, x_71);
x_26 = x_73;
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
lean_inc(x_28);
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
lean_inc(x_1);
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
lean_inc(x_1);
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
lean_inc(x_50);
x_51 = lean_ctor_get(x_28, 2);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_28, sizeof(void*)*5);
x_53 = lean_ctor_get_uint8(x_28, sizeof(void*)*5 + 1);
x_54 = lean_ctor_get(x_28, 3);
lean_inc(x_54);
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
lean_inc(x_1);
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
lean_dec(x_28);
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
x_11 = l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0;
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
lean_object* x_6; lean_object* x_7; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_string_utf8_byte_size(x_2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_29 = l_Lake_compileLeanModule___lam__0___closed__1;
x_30 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_2, x_26, x_27);
x_31 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_2, x_30, x_26);
x_32 = lean_string_utf8_extract(x_2, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = lean_string_append(x_29, x_32);
lean_dec(x_32);
x_34 = lean_box(1);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_array_push(x_4, x_35);
x_6 = x_37;
x_7 = x_5;
goto block_25;
}
else
{
lean_dec(x_26);
x_6 = x_4;
x_7 = x_5;
goto block_25;
}
block_25:
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = l_Lake_compileLeanModule___lam__0___closed__0;
x_15 = lean_uint32_to_nat(x_1);
x_16 = l_Nat_reprFast(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = lean_box(3);
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = lean_array_get_size(x_6);
x_22 = lean_array_push(x_6, x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
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
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
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
x_1 = lean_mk_string_unchecked("-R", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-o", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_compileLeanModule___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__18;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_compileLeanModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_139 = lean_ctor_get(x_5, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_5, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_5, 5);
lean_inc(x_141);
x_142 = lean_ctor_get(x_5, 6);
lean_inc(x_142);
lean_dec(x_5);
x_230 = l_Lake_compileLeanModule___closed__16;
x_231 = l_Lake_compileLeanModule___closed__17;
x_232 = lean_array_push(x_231, x_1);
x_233 = lean_array_push(x_232, x_230);
x_234 = lean_array_push(x_233, x_8);
x_235 = l_Array_append___redArg(x_6, x_234);
lean_dec(x_234);
if (lean_obj_tag(x_139) == 0)
{
x_201 = x_235;
x_202 = x_10;
x_203 = x_11;
goto block_229;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_139, 0);
lean_inc(x_236);
lean_dec(x_139);
x_237 = l_Lake_createParentDirs(x_236, x_11);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_239 = l_Lake_compileLeanModule___closed__19;
x_240 = lean_array_push(x_239, x_236);
x_241 = l_Array_append___redArg(x_235, x_240);
lean_dec(x_240);
x_201 = x_241;
x_202 = x_10;
x_203 = x_238;
goto block_229;
}
else
{
uint8_t x_242; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_242 = !lean_is_exclusive(x_237);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_237, 0);
x_244 = lean_io_error_to_string(x_243);
x_245 = lean_box(3);
x_246 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_246, 0, x_244);
x_247 = lean_unbox(x_245);
lean_ctor_set_uint8(x_246, sizeof(void*)*1, x_247);
x_248 = lean_array_get_size(x_10);
x_249 = lean_array_push(x_10, x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set_tag(x_237, 0);
lean_ctor_set(x_237, 0, x_250);
return x_237;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_251 = lean_ctor_get(x_237, 0);
x_252 = lean_ctor_get(x_237, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_237);
x_253 = lean_io_error_to_string(x_251);
x_254 = lean_box(3);
x_255 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_255, 0, x_253);
x_256 = lean_unbox(x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_256);
x_257 = lean_array_get_size(x_10);
x_258 = lean_array_push(x_10, x_255);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_252);
return x_260;
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
block_23:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_20);
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_12 = x_18;
x_13 = x_22;
x_14 = x_21;
goto block_17;
}
}
block_138:
{
lean_object* x_27; 
x_27 = l_Lake_createParentDirs(x_4, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Setup_0__Lean_toJsonModuleSetup____x40_Lean_Setup___hyg_1598_(x_3);
x_30 = lean_unsigned_to_nat(80u);
x_31 = l_Lean_Json_pretty(x_29, x_30);
x_32 = l_IO_FS_writeFile(x_4, x_31, x_28);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lake_compileLeanModule___closed__2;
x_35 = lean_array_push(x_34, x_4);
x_36 = l_Array_append___redArg(x_24, x_35);
lean_dec(x_35);
x_37 = l_Lake_compileLeanModule___closed__3;
x_38 = lean_array_push(x_36, x_37);
x_39 = l_Lake_compileLeanModule___closed__4;
x_40 = lean_box(0);
x_41 = l_Lake_compileLeanModule___closed__5;
x_42 = l_System_SearchPath_toString(x_7);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lake_compileLeanModule___closed__6;
x_46 = lean_array_push(x_45, x_44);
x_47 = lean_box(1);
x_48 = lean_box(0);
lean_inc(x_9);
x_49 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_9);
lean_ctor_set(x_49, 2, x_38);
lean_ctor_set(x_49, 3, x_40);
lean_ctor_set(x_49, 4, x_46);
x_50 = lean_unbox(x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*5, x_50);
x_51 = lean_unbox(x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*5 + 1, x_51);
x_52 = lean_array_get_size(x_25);
lean_inc(x_49);
x_53 = l_Lake_mkCmdLog(x_49);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_array_push(x_25, x_55);
x_58 = l_IO_Process_output(x_49, x_33);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint32_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_9);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get_uint32(x_59, sizeof(void*)*2);
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_string_utf8_byte_size(x_62);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_67 = l_Lake_compileLeanModule___closed__7;
x_68 = l_String_split___at___Lean_stringToMessageData_spec__0(x_62);
lean_dec(x_62);
x_69 = l_List_foldlM___at___Lake_compileLeanModule_spec__0(x_2, x_67, x_68, x_57, x_60);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_string_utf8_byte_size(x_72);
x_75 = lean_nat_dec_eq(x_74, x_65);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1;
x_77 = lean_string_append(x_76, x_72);
lean_dec(x_72);
x_78 = lean_box(1);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
x_80 = lean_unbox(x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_80);
x_81 = lean_box(0);
x_82 = lean_array_push(x_73, x_79);
x_83 = l_Lake_compileLeanModule___lam__0(x_61, x_63, x_81, x_82, x_71);
lean_dec(x_63);
x_18 = x_52;
x_19 = x_83;
goto block_23;
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_72);
x_84 = lean_box(0);
x_85 = l_Lake_compileLeanModule___lam__0(x_61, x_63, x_84, x_73, x_71);
lean_dec(x_63);
x_18 = x_52;
x_19 = x_85;
goto block_23;
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_62);
lean_dec(x_2);
x_86 = lean_box(0);
x_87 = l_Lake_compileLeanModule___lam__0(x_61, x_63, x_86, x_57, x_60);
lean_dec(x_63);
x_18 = x_52;
x_19 = x_87;
goto block_23;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_2);
x_88 = lean_ctor_get(x_58, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_58, 1);
lean_inc(x_89);
lean_dec(x_58);
x_90 = l_Lake_compileLeanModule___closed__8;
x_91 = lean_string_append(x_90, x_9);
lean_dec(x_9);
x_92 = l_Lake_compileLeanModule___closed__9;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_io_error_to_string(x_88);
x_95 = lean_string_append(x_93, x_94);
lean_dec(x_94);
x_96 = lean_box(3);
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
x_98 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_98);
x_99 = lean_array_push(x_57, x_97);
x_12 = x_52;
x_13 = x_99;
x_14 = x_89;
goto block_17;
}
}
else
{
uint8_t x_100; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_32);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_32, 0);
x_102 = lean_io_error_to_string(x_101);
x_103 = lean_box(3);
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_unbox(x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
x_106 = lean_array_get_size(x_25);
x_107 = lean_array_push(x_25, x_104);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_tag(x_32, 0);
lean_ctor_set(x_32, 0, x_108);
return x_32;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_109 = lean_ctor_get(x_32, 0);
x_110 = lean_ctor_get(x_32, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_32);
x_111 = lean_io_error_to_string(x_109);
x_112 = lean_box(3);
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_114);
x_115 = lean_array_get_size(x_25);
x_116 = lean_array_push(x_25, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_110);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_27);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_120 = lean_ctor_get(x_27, 0);
x_121 = lean_io_error_to_string(x_120);
x_122 = lean_box(3);
x_123 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_123, 0, x_121);
x_124 = lean_unbox(x_122);
lean_ctor_set_uint8(x_123, sizeof(void*)*1, x_124);
x_125 = lean_array_get_size(x_25);
x_126 = lean_array_push(x_25, x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_127);
return x_27;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_128 = lean_ctor_get(x_27, 0);
x_129 = lean_ctor_get(x_27, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_27);
x_130 = lean_io_error_to_string(x_128);
x_131 = lean_box(3);
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_130);
x_133 = lean_unbox(x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_133);
x_134 = lean_array_get_size(x_25);
x_135 = lean_array_push(x_25, x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_129);
return x_137;
}
}
}
block_171:
{
if (lean_obj_tag(x_142) == 0)
{
x_24 = x_143;
x_25 = x_144;
x_26 = x_145;
goto block_138;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
lean_dec(x_142);
x_147 = l_Lake_createParentDirs(x_146, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lake_compileLeanModule___closed__11;
x_150 = lean_array_push(x_149, x_146);
x_151 = l_Array_append___redArg(x_143, x_150);
lean_dec(x_150);
x_24 = x_151;
x_25 = x_144;
x_26 = x_148;
goto block_138;
}
else
{
uint8_t x_152; 
lean_dec(x_146);
lean_dec(x_143);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_147);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_147, 0);
x_154 = lean_io_error_to_string(x_153);
x_155 = lean_box(3);
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
x_157 = lean_unbox(x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_157);
x_158 = lean_array_get_size(x_144);
x_159 = lean_array_push(x_144, x_156);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_tag(x_147, 0);
lean_ctor_set(x_147, 0, x_160);
return x_147;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_147, 0);
x_162 = lean_ctor_get(x_147, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_147);
x_163 = lean_io_error_to_string(x_161);
x_164 = lean_box(3);
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_unbox(x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_166);
x_167 = lean_array_get_size(x_144);
x_168 = lean_array_push(x_144, x_165);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_162);
return x_170;
}
}
}
}
block_200:
{
if (lean_obj_tag(x_141) == 0)
{
x_143 = x_172;
x_144 = x_173;
x_145 = x_174;
goto block_171;
}
else
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_141, 0);
lean_inc(x_175);
lean_dec(x_141);
x_176 = l_Lake_createParentDirs(x_175, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lake_compileLeanModule___closed__13;
x_179 = lean_array_push(x_178, x_175);
x_180 = l_Array_append___redArg(x_172, x_179);
lean_dec(x_179);
x_143 = x_180;
x_144 = x_173;
x_145 = x_177;
goto block_171;
}
else
{
uint8_t x_181; 
lean_dec(x_175);
lean_dec(x_172);
lean_dec(x_142);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_176);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = lean_ctor_get(x_176, 0);
x_183 = lean_io_error_to_string(x_182);
x_184 = lean_box(3);
x_185 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_185, 0, x_183);
x_186 = lean_unbox(x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_186);
x_187 = lean_array_get_size(x_173);
x_188 = lean_array_push(x_173, x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set_tag(x_176, 0);
lean_ctor_set(x_176, 0, x_189);
return x_176;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_190 = lean_ctor_get(x_176, 0);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_176);
x_192 = lean_io_error_to_string(x_190);
x_193 = lean_box(3);
x_194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_194, 0, x_192);
x_195 = lean_unbox(x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*1, x_195);
x_196 = lean_array_get_size(x_173);
x_197 = lean_array_push(x_173, x_194);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_191);
return x_199;
}
}
}
}
block_229:
{
if (lean_obj_tag(x_140) == 0)
{
x_172 = x_201;
x_173 = x_202;
x_174 = x_203;
goto block_200;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_140, 0);
lean_inc(x_204);
lean_dec(x_140);
x_205 = l_Lake_createParentDirs(x_204, x_203);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = l_Lake_compileLeanModule___closed__15;
x_208 = lean_array_push(x_207, x_204);
x_209 = l_Array_append___redArg(x_201, x_208);
lean_dec(x_208);
x_172 = x_209;
x_173 = x_202;
x_174 = x_206;
goto block_200;
}
else
{
uint8_t x_210; 
lean_dec(x_204);
lean_dec(x_201);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_210 = !lean_is_exclusive(x_205);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_ctor_get(x_205, 0);
x_212 = lean_io_error_to_string(x_211);
x_213 = lean_box(3);
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_215);
x_216 = lean_array_get_size(x_202);
x_217 = lean_array_push(x_202, x_214);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set_tag(x_205, 0);
lean_ctor_set(x_205, 0, x_218);
return x_205;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_219 = lean_ctor_get(x_205, 0);
x_220 = lean_ctor_get(x_205, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_205);
x_221 = lean_io_error_to_string(x_219);
x_222 = lean_box(3);
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_221);
x_224 = lean_unbox(x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_224);
x_225 = lean_array_get_size(x_202);
x_226 = lean_array_push(x_202, x_223);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_220);
return x_228;
}
}
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
x_7 = l_Lake_compileLeanModule___lam__0(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
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
x_1 = l_Lake_compileLeanModule___closed__18;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_compileLeanModule___closed__4;
x_10 = l_Lake_compileO___closed__2;
x_11 = lean_array_push(x_10, x_1);
x_12 = lean_array_push(x_11, x_2);
x_13 = l_Array_append___redArg(x_12, x_3);
x_14 = lean_box(0);
x_15 = l_Lake_compileO___closed__3;
x_16 = lean_box(1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_4);
lean_ctor_set(x_18, 2, x_13);
lean_ctor_set(x_18, 3, x_14);
lean_ctor_set(x_18, 4, x_15);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_19);
x_20 = lean_unbox(x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*5 + 1, x_20);
x_21 = lean_unbox(x_17);
x_22 = l_Lake_proc(x_18, x_21, x_5, x_8);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_io_error_to_string(x_24);
x_26 = lean_box(3);
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
x_29 = lean_array_get_size(x_5);
x_30 = lean_array_push(x_5, x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_io_error_to_string(x_32);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_5);
x_39 = lean_array_push(x_5, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
x_10 = l_Lake_compileLeanModule___closed__7;
x_11 = lean_string_utf8_byte_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_String_foldlAux___at___Lake_mkArgs_spec__0(x_9, x_11, x_12, x_10);
lean_dec(x_11);
lean_dec(x_9);
x_14 = l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1;
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = lean_box(3);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_array_get_size(x_6);
x_31 = lean_array_push(x_6, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_32);
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_io_error_to_string(x_33);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_6);
x_40 = lean_array_push(x_6, x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_5);
lean_ctor_set(x_43, 1, x_6);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_8 = l_Lake_mkArgs___closed__0;
x_9 = l_System_FilePath_addExtension(x_1, x_8);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = lean_io_prim_handle_mk(x_9, x_20, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_array_get_size(x_2);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_2);
x_10 = x_3;
x_11 = x_23;
goto block_18;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_2);
x_10 = x_3;
x_11 = x_23;
goto block_18;
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_box(0);
x_29 = 0;
x_30 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_31 = l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(x_22, x_2, x_29, x_30, x_28, x_3, x_23);
lean_dec(x_2);
lean_dec(x_22);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_10 = x_34;
x_11 = x_33;
goto block_18;
}
else
{
uint8_t x_35; 
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_31, 0, x_40);
return x_31;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_44 = x_32;
} else {
 lean_dec_ref(x_32);
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
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_io_error_to_string(x_48);
x_50 = lean_box(3);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
x_53 = lean_array_get_size(x_3);
x_54 = lean_array_push(x_3, x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_55);
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_io_error_to_string(x_56);
x_59 = lean_box(3);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_array_get_size(x_3);
x_63 = lean_array_push(x_3, x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_57);
return x_65;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lake_mkArgs___closed__1;
x_13 = lean_string_append(x_12, x_9);
lean_dec(x_9);
x_14 = l_Lake_mkArgs___closed__2;
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
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lake_compileStaticLib(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_createParentDirs(x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_compileStaticLib___closed__1;
x_10 = lean_box(1);
if (x_4 == 0)
{
x_11 = x_9;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = l_Lake_compileStaticLib___closed__3;
x_11 = x_44;
goto block_43;
}
block_43:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_size(x_2);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(x_12, x_13, x_2);
lean_inc(x_1);
x_15 = l_Lake_mkArgs(x_1, x_14, x_5, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_array_push(x_11, x_1);
x_21 = l_Array_append___redArg(x_20, x_18);
lean_dec(x_18);
x_22 = l_Lake_compileLeanModule___closed__4;
x_23 = lean_box(0);
x_24 = l_Lake_compileO___closed__3;
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
x_27 = lean_unbox(x_10);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_27);
x_28 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5 + 1, x_28);
x_29 = lean_unbox(x_25);
x_30 = l_Lake_proc(x_26, x_29, x_19, x_17);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_15, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_15, 0, x_36);
return x_15;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_dec(x_15);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_40 = x_16;
} else {
 lean_dec_ref(x_16);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_io_error_to_string(x_46);
x_48 = lean_box(3);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
x_50 = lean_unbox(x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_50);
x_51 = lean_array_get_size(x_5);
x_52 = lean_array_push(x_5, x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_io_error_to_string(x_54);
x_57 = lean_box(3);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = lean_array_get_size(x_5);
x_61 = lean_array_push(x_5, x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_55);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_compileStaticLib_spec__0(x_4, x_5, x_3);
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
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
x_5 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__0;
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
x_10 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv___closed__4;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileSharedLib___closed__0;
x_2 = l_Lake_compileLeanModule___closed__17;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_compileSharedLib___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_compileLeanModule___closed__18;
x_2 = l_Lake_compileSharedLib___closed__1;
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
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lake_mkArgs(x_1, x_2, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_compileLeanModule___closed__4;
x_17 = l_Lake_compileSharedLib___closed__2;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Array_append___redArg(x_18, x_11);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = lean_box(1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_14);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_24);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_25);
x_26 = lean_unbox(x_22);
x_27 = l_Lake_proc(x_23, x_26, x_12, x_15);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_8, 0, x_33);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_37 = x_9;
} else {
 lean_dec_ref(x_9);
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
uint8_t x_40; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_io_error_to_string(x_41);
x_43 = lean_box(3);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_array_get_size(x_4);
x_47 = lean_array_push(x_4, x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_48);
return x_6;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = lean_io_error_to_string(x_49);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_4);
x_56 = lean_array_push(x_4, x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
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
lean_dec(x_6);
lean_inc(x_1);
x_8 = l_Lake_mkArgs(x_1, x_2, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l___private_Lake_Build_Actions_0__Lake_getMacOSXDeploymentEnv(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lake_compileLeanModule___closed__4;
x_17 = l_Lake_compileLeanModule___closed__19;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Array_append___redArg(x_18, x_11);
lean_dec(x_11);
x_20 = lean_box(0);
x_21 = lean_box(1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_14);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_24);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*5 + 1, x_25);
x_26 = lean_unbox(x_22);
x_27 = l_Lake_proc(x_23, x_26, x_12, x_15);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_8, 0, x_33);
return x_8;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_37 = x_9;
} else {
 lean_dec_ref(x_9);
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
uint8_t x_40; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_io_error_to_string(x_41);
x_43 = lean_box(3);
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_array_get_size(x_4);
x_47 = lean_array_push(x_4, x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_48);
return x_6;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_6, 0);
x_50 = lean_ctor_get(x_6, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_6);
x_51 = lean_io_error_to_string(x_49);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_4);
x_56 = lean_array_push(x_4, x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-H", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0;
x_2 = l_Lake_compileLeanModule___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Array_append___redArg(x_4, x_8);
lean_dec(x_8);
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
x_1 = l_Lake_compileLeanModule___closed__18;
x_2 = l_Lake_download___closed__8;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_download(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_21; lean_object* x_22; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_System_FilePath_pathExists(x_2, x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
x_41 = lean_ctor_get(x_36, 0);
lean_dec(x_41);
x_42 = l_Lake_createParentDirs(x_2, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_free_object(x_36);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_21 = x_4;
x_22 = x_43;
goto block_35;
}
else
{
uint8_t x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_io_error_to_string(x_45);
x_47 = lean_box(3);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_array_get_size(x_4);
x_51 = lean_array_push(x_4, x_48);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_51);
lean_ctor_set(x_36, 0, x_50);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_36);
return x_42;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_array_get_size(x_4);
x_59 = lean_array_push(x_4, x_56);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_59);
lean_ctor_set(x_36, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_36);
lean_ctor_set(x_60, 1, x_53);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_dec(x_36);
x_62 = l_Lake_createParentDirs(x_2, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_21 = x_4;
x_22 = x_63;
goto block_35;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_66 = x_62;
} else {
 lean_dec_ref(x_62);
 x_66 = lean_box(0);
}
x_67 = lean_io_error_to_string(x_64);
x_68 = lean_box(3);
x_69 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_unbox(x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
x_71 = lean_array_get_size(x_4);
x_72 = lean_array_push(x_4, x_69);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_66)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_66;
 lean_ctor_set_tag(x_74, 0);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_65);
return x_74;
}
}
}
else
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_36);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_36, 1);
x_77 = lean_ctor_get(x_36, 0);
lean_dec(x_77);
x_78 = lean_io_remove_file(x_2, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_free_object(x_36);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_21 = x_4;
x_22 = x_79;
goto block_35;
}
else
{
uint8_t x_80; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_io_error_to_string(x_81);
x_83 = lean_box(3);
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
x_86 = lean_array_get_size(x_4);
x_87 = lean_array_push(x_4, x_84);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_87);
lean_ctor_set(x_36, 0, x_86);
lean_ctor_set_tag(x_78, 0);
lean_ctor_set(x_78, 0, x_36);
return x_78;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_ctor_get(x_78, 0);
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_78);
x_90 = lean_io_error_to_string(x_88);
x_91 = lean_box(3);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
x_93 = lean_unbox(x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_93);
x_94 = lean_array_get_size(x_4);
x_95 = lean_array_push(x_4, x_92);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_95);
lean_ctor_set(x_36, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_36);
lean_ctor_set(x_96, 1, x_89);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_36, 1);
lean_inc(x_97);
lean_dec(x_36);
x_98 = lean_io_remove_file(x_2, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_21 = x_4;
x_22 = x_99;
goto block_35;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_102 = x_98;
} else {
 lean_dec_ref(x_98);
 x_102 = lean_box(0);
}
x_103 = lean_io_error_to_string(x_100);
x_104 = lean_box(3);
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
x_106 = lean_unbox(x_104);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_106);
x_107 = lean_array_get_size(x_4);
x_108 = lean_array_push(x_4, x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_102;
 lean_ctor_set_tag(x_110, 0);
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_101);
return x_110;
}
}
}
block_20:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_9 = l_Lake_compileLeanModule___closed__4;
x_10 = l_Lake_download___closed__0;
x_11 = lean_box(0);
x_12 = l_Lake_compileO___closed__3;
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_17);
x_18 = lean_unbox(x_13);
x_19 = l_Lake_proc(x_15, x_18, x_6, x_7);
return x_19;
}
block_35:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = l_Lake_download___closed__4;
x_24 = l_Lake_download___closed__9;
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_array_push(x_26, x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_3);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
lean_dec(x_29);
x_6 = x_21;
x_7 = x_22;
x_8 = x_27;
goto block_20;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_29, x_29);
if (x_31 == 0)
{
lean_dec(x_29);
x_6 = x_21;
x_7 = x_22;
x_8 = x_27;
goto block_20;
}
else
{
size_t x_32; size_t x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_34 = l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0(x_3, x_32, x_33, x_27);
x_6 = x_21;
x_7 = x_22;
x_8 = x_34;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_30; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_30 = l_Lake_untar___closed__3;
if (x_3 == 0)
{
x_8 = x_30;
x_9 = x_4;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = l_Lake_untar___closed__4;
x_8 = x_31;
x_9 = x_4;
goto block_29;
}
block_29:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
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
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_20);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_unbox(x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*5, x_25);
x_26 = lean_unbox(x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*5 + 1, x_26);
x_27 = lean_unbox(x_22);
x_28 = l_Lake_proc(x_24, x_27, x_9, x_7);
return x_28;
}
}
else
{
uint8_t x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_6, 0);
x_34 = lean_io_error_to_string(x_33);
x_35 = lean_box(3);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
x_38 = lean_array_get_size(x_4);
x_39 = lean_array_push(x_4, x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 0, x_40);
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_io_error_to_string(x_41);
x_44 = lean_box(3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_array_get_size(x_4);
x_48 = lean_array_push(x_4, x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
}
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
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--exclude=", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lake_tar(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; 
x_20 = l_Lake_createParentDirs(x_2, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_49; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_49 = l_Lake_tar___closed__8;
if (x_3 == 0)
{
x_22 = x_49;
x_23 = x_5;
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = l_Lake_tar___closed__10;
x_22 = x_50;
x_23 = x_5;
goto block_48;
}
block_48:
{
size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_24 = lean_array_size(x_4);
x_25 = 0;
x_26 = l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(x_4, x_24, x_25, x_22, x_23, x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lake_compileLeanModule___closed__4;
x_32 = l_Lake_untar___closed__0;
x_33 = l_Lake_untar___closed__1;
x_34 = l_Lake_tar___closed__0;
x_35 = l_Lake_tar___closed__1;
x_36 = lean_array_push(x_35, x_2);
x_37 = lean_array_push(x_36, x_33);
x_38 = lean_array_push(x_37, x_1);
x_39 = lean_array_push(x_38, x_34);
x_40 = l_Array_append___redArg(x_29, x_39);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = l_System_Platform_isOSX;
x_43 = lean_box(1);
if (x_42 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Lake_compileO___closed__3;
x_45 = lean_unbox(x_43);
x_7 = x_41;
x_8 = x_45;
x_9 = x_32;
x_10 = x_40;
x_11 = x_30;
x_12 = x_31;
x_13 = x_28;
x_14 = x_44;
goto block_19;
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Lake_tar___closed__6;
x_47 = lean_unbox(x_43);
x_7 = x_41;
x_8 = x_47;
x_9 = x_32;
x_10 = x_40;
x_11 = x_30;
x_12 = x_31;
x_13 = x_28;
x_14 = x_46;
goto block_19;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_io_error_to_string(x_52);
x_54 = lean_box(3);
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_53);
x_56 = lean_unbox(x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
x_57 = lean_array_get_size(x_5);
x_58 = lean_array_push(x_5, x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_59);
return x_20;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_60 = lean_ctor_get(x_20, 0);
x_61 = lean_ctor_get(x_20, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_20);
x_62 = lean_io_error_to_string(x_60);
x_63 = lean_box(3);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = lean_array_get_size(x_5);
x_67 = lean_array_push(x_5, x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_61);
return x_69;
}
}
block_19:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_7);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_8);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*5 + 1, x_17);
x_18 = l_Lake_proc(x_16, x_8, x_11, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
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
lean_object* initialize_Lean_Setup(uint8_t builtin, lean_object*);
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
l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__0);
l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1 = _init_l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1();
lean_mark_persistent(l_List_foldlM___at___Lake_compileLeanModule_spec__0___closed__1);
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
l_Lake_compileLeanModule___closed__18 = _init_l_Lake_compileLeanModule___closed__18();
lean_mark_persistent(l_Lake_compileLeanModule___closed__18);
l_Lake_compileLeanModule___closed__19 = _init_l_Lake_compileLeanModule___closed__19();
lean_mark_persistent(l_Lake_compileLeanModule___closed__19);
l_Lake_compileO___closed__0 = _init_l_Lake_compileO___closed__0();
lean_mark_persistent(l_Lake_compileO___closed__0);
l_Lake_compileO___closed__1 = _init_l_Lake_compileO___closed__1();
lean_mark_persistent(l_Lake_compileO___closed__1);
l_Lake_compileO___closed__2 = _init_l_Lake_compileO___closed__2();
lean_mark_persistent(l_Lake_compileO___closed__2);
l_Lake_compileO___closed__3 = _init_l_Lake_compileO___closed__3();
lean_mark_persistent(l_Lake_compileO___closed__3);
l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__0);
l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_mkArgs_spec__1___closed__1);
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
l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__0);
l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lake_download_spec__0___closed__1);
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
l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lake_tar_spec__0___closed__0);
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
