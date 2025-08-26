// Lean compiler output
// Module: Lean.Util.Path
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__4;
LEAN_EXPORT lean_object* l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___closed__3;
LEAN_EXPORT lean_object* lean_init_search_path(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static uint8_t l_Lean_getLibDir___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findLean___closed__0;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initSearchPath___closed__0;
static lean_object* l_Lean_addSearchPathFromEnv___closed__0;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_moduleNameOfFileName___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_SearchPath_parse(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___closed__0;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__2;
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__4;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_findSysroot___closed__1;
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__1;
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__3;
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__0;
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath(lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__0;
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
lean_object* lean_mk_io_user_error(lean_object*);
static uint32_t l_Lean_moduleNameOfFileName___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getLibDir___closed__3;
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_findOLean_spec__0(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
static lean_object* l_Lean_getLibDir___closed__0;
static lean_object* l_Lean_getBuildDir___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___closed__5;
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_prefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0;
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchPathRef;
static lean_object* l_Lean_findOLean___closed__5;
static lean_object* l_Lean_findSysroot___closed__4;
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Substring_prevn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__7;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0;
uint8_t l_Substring_beq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_current_dir(lean_object*);
static lean_object* l_Lean_findSysroot___closed__2;
static lean_object* l_Lean_getLibDir___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_searchModuleNameOfFileName___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_libdir(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__0;
lean_object* l_IO_Process_run(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__0;
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__1;
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__6;
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_moduleNameOfFileName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_System_FilePath_isDir(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Name_append(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12) {
_start:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__0;
x_14 = l_System_FilePath_extension(x_1);
x_15 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__2;
x_16 = l_Option_beqOption___redArg____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3_(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_17 = lean_apply_2(x_2, lean_box(0), x_3);
x_18 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_6);
x_20 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_21 = l_System_FilePath_withExtension(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Name_str___override(x_22, x_21);
x_24 = lean_apply_1(x_7, x_23);
x_25 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_8);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_26 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_6);
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_26);
x_29 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__1), 3, 2);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_7);
x_30 = l_Lean_forEachModuleInDir___redArg(x_9, x_10, x_1, x_29);
x_31 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_30, x_11);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc_ref(x_10);
x_13 = l_IO_FS_DirEntry_path(x_10);
lean_inc_ref(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__3___boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
lean_inc(x_8);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__2___boxed), 12, 11);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_4);
lean_closure_set(x_15, 5, x_10);
lean_closure_set(x_15, 6, x_5);
lean_closure_set(x_15, 7, x_6);
lean_closure_set(x_15, 8, x_7);
lean_closure_set(x_15, 9, x_8);
lean_closure_set(x_15, 10, x_9);
x_16 = lean_apply_2(x_8, lean_box(0), x_14);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_inc_ref(x_4);
lean_inc_ref_n(x_8, 2);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__4), 12, 9);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_7);
lean_closure_set(x_9, 2, x_2);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_3);
lean_closure_set(x_9, 5, x_8);
lean_closure_set(x_9, 6, x_4);
lean_closure_set(x_9, 7, x_5);
lean_closure_set(x_9, 8, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__5), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_7);
x_11 = lean_array_size(x_6);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_6, x_9, x_11, x_12, x_7);
x_14 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_13, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_System_FilePath_readDir___boxed), 2, 1);
lean_closure_set(x_8, 0, x_3);
lean_inc(x_2);
x_9 = lean_apply_2(x_2, lean_box(0), x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___redArg___lam__6), 6, 5);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_1);
lean_closure_set(x_10, 4, x_2);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_forEachModuleInDir___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_forEachModuleInDir___redArg___lam__3(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_12);
x_14 = l_Lean_forEachModuleInDir___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_System_FilePath_normalize(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_System_FilePath_normalize(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Util.Path", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.modToFilePath.go", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed import", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2;
x_2 = lean_unsigned_to_nat(20u);
x_3 = lean_unsigned_to_nat(44u);
x_4 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1;
x_5 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_inc_ref(x_1);
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(x_1, x_3);
x_6 = l_System_FilePath_join(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3;
x_8 = l_panic___at_____private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(x_1, x_2);
x_5 = l_System_FilePath_addExtension(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_modToFilePath(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_9 = x_3;
} else {
 lean_dec_ref(x_3);
 x_9 = lean_box(0);
}
lean_inc(x_7);
x_14 = l_System_FilePath_join(x_7, x_1);
x_15 = l_System_FilePath_isDir(x_14, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_System_FilePath_addExtension(x_14, x_2);
x_20 = l_System_FilePath_pathExists(x_19, x_18);
lean_dec_ref(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_7);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec_ref(x_20);
x_3 = x_8;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec_ref(x_20);
x_10 = x_25;
goto block_13;
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_14);
lean_dec(x_8);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec_ref(x_15);
x_10 = x_26;
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
if (lean_is_scalar(x_9)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_9;
 lean_ctor_set_tag(x_12, 0);
}
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = 0;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0(x_7, x_2, x_1, x_4);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = l_Lean_modToFilePath(x_13, x_3, x_2);
lean_dec(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lean_modToFilePath(x_15, x_3, x_2);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
x_21 = l_Lean_modToFilePath(x_19, x_3, x_2);
lean_dec(x_19);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at___Lean_SearchPath_findWithExt_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_5 = x_11;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_System_FilePath_pathExists(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec_ref(x_10);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
x_5 = x_17;
goto block_8;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
lean_ctor_set(x_14, 0, x_10);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findModuleWithExt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_string_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_12);
x_13 = l_System_FilePath_extension(x_12);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0(x_13, x_14);
lean_dec_ref(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_dec_ref(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_12);
x_6 = x_16;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc_ref(x_12);
x_13 = l_System_FilePath_extension(x_12);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0(x_13, x_14);
lean_dec_ref(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_dec_ref(x_12);
x_6 = x_5;
goto block_10;
}
else
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_12);
x_6 = x_16;
goto block_10;
}
}
else
{
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1(x_1, x_2, x_8, x_4, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_System_FilePath_isDir(x_6, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_6);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_2 = x_7;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = l_System_FilePath_walkDir(x_6, x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_16);
x_24 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0;
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_16);
x_18 = x_24;
goto block_21;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_23, x_23);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_16);
x_18 = x_24;
goto block_21;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_23);
lean_dec(x_23);
lean_inc_ref(x_1);
x_29 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1(x_1, x_16, x_27, x_28, x_24);
lean_dec(x_16);
x_18 = x_29;
goto block_21;
}
}
block_21:
{
lean_object* x_19; 
x_19 = l_Array_append___redArg(x_3, x_18);
lean_dec_ref(x_18);
x_2 = x_7;
x_3 = x_19;
x_4 = x_17;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg(x_1, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec_ref(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = l_System_FilePath_isDir(x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg(x_1, x_8, x_4, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec_ref(x_9);
x_15 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_15, 0, x_10);
x_16 = l_System_FilePath_walkDir(x_7, x_15, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_17);
x_25 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0;
x_26 = lean_nat_dec_lt(x_23, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_17);
x_19 = x_25;
goto block_22;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_24, x_24);
if (x_27 == 0)
{
lean_dec(x_24);
lean_dec(x_17);
x_19 = x_25;
goto block_22;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc_ref(x_1);
x_30 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1(x_1, x_17, x_28, x_29, x_25);
lean_dec(x_17);
x_19 = x_30;
goto block_22;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Array_append___redArg(x_4, x_19);
lean_dec_ref(x_19);
x_21 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg(x_1, x_8, x_20, x_18);
return x_21;
}
}
else
{
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0;
lean_inc(x_1);
x_5 = l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg(x_2, x_1, x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lean_SearchPath_findAllWithExt_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SearchPath_findAllWithExt_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___lam__0(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_getBuildDir___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(23u);
x_4 = l_Lean_getBuildDir___closed__1;
x_5 = l_Lean_getBuildDir___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_get_prefix(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_appDir(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_System_FilePath_parent(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_getBuildDir___closed__3;
x_7 = l_panic___at_____private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_System_FilePath_parent(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_getBuildDir___closed__3;
x_13 = l_panic___at_____private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec_ref(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Lean_getLibDir___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static uint8_t _init_l_Lean_getLibDir___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_stage0(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("..", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stage1", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_get_libdir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_11; 
x_11 = l_Lean_getLibDir___closed__1;
if (x_11 == 0)
{
x_3 = x_1;
x_4 = x_2;
goto block_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Lean_getLibDir___closed__2;
x_13 = l_System_FilePath_join(x_1, x_12);
x_14 = l_Lean_getLibDir___closed__3;
x_15 = l_System_FilePath_join(x_13, x_14);
x_3 = x_15;
x_4 = x_2;
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_getLibDir___closed__0;
x_6 = l_System_FilePath_join(x_3, x_5);
x_7 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_8 = l_System_FilePath_join(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_get_libdir(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
static lean_object* _init_l_Lean_addSearchPathFromEnv___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_PATH", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_addSearchPathFromEnv___closed__0;
x_4 = lean_io_getenv(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec_ref(x_5);
x_13 = l_System_SearchPath_parse(x_12);
lean_dec(x_12);
x_14 = l_List_appendTR___redArg(x_13, x_1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = l_System_SearchPath_parse(x_16);
lean_dec(x_16);
x_18 = l_List_appendTR___redArg(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_initSearchPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_searchPathRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lean_getBuiltinSearchPath(x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_addSearchPathFromEnv(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_List_appendTR___redArg(x_2, x_8);
x_11 = l_Lean_initSearchPath___closed__0;
x_12 = lean_st_ref_set(x_11, x_10, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* lean_init_search_path(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_prefix(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_Lean_initSearchPath(x_3, x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_findOLean_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_findOLean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown module prefix '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n\nNo directory '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' or file '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".olean' in the search path entries:\n", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_initSearchPath___closed__0;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_findOLean___closed__0;
lean_inc(x_5);
x_8 = l_Lean_SearchPath_findWithExt(x_5, x_7, x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_Name_getRoot(x_1);
x_13 = 0;
x_14 = l_Lean_Name_toString(x_12, x_13);
x_15 = l_Lean_findOLean___closed__1;
x_16 = lean_string_append(x_15, x_14);
x_17 = l_Lean_findOLean___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_14);
x_20 = l_Lean_findOLean___closed__3;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_14);
lean_dec_ref(x_14);
x_23 = l_Lean_findOLean___closed__4;
x_24 = lean_string_append(x_22, x_23);
x_25 = l_Lean_findOLean___closed__5;
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___Lean_findOLean_spec__0(x_5, x_26);
x_28 = l_String_intercalate(x_25, x_27);
x_29 = lean_string_append(x_24, x_28);
lean_dec_ref(x_28);
x_30 = lean_mk_io_user_error(x_29);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Lean_Name_getRoot(x_1);
x_33 = 0;
x_34 = l_Lean_Name_toString(x_32, x_33);
x_35 = l_Lean_findOLean___closed__1;
x_36 = lean_string_append(x_35, x_34);
x_37 = l_Lean_findOLean___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_34);
x_40 = l_Lean_findOLean___closed__3;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_34);
lean_dec_ref(x_34);
x_43 = l_Lean_findOLean___closed__4;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_Lean_findOLean___closed__5;
x_46 = lean_box(0);
x_47 = l_List_mapTR_loop___at___Lean_findOLean_spec__0(x_5, x_46);
x_48 = l_String_intercalate(x_45, x_47);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = lean_mk_io_user_error(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_8);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_8, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_9, 0);
lean_inc(x_54);
lean_dec_ref(x_9);
lean_ctor_set(x_8, 0, x_54);
return x_8;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_8, 1);
lean_inc(x_55);
lean_dec(x_8);
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec_ref(x_9);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_findOLean(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_findLean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lean' in the search path entries:\n", 35, 35);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
lean_inc(x_1);
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_Name_getRoot(x_2);
x_10 = 0;
x_11 = l_Lean_Name_toString(x_9, x_10);
x_12 = l_Lean_findOLean___closed__1;
x_13 = lean_string_append(x_12, x_11);
x_14 = l_Lean_findOLean___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_11);
x_17 = l_Lean_findOLean___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_11);
lean_dec_ref(x_11);
x_20 = l_Lean_findLean___closed__0;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Lean_findOLean___closed__5;
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at___Lean_findOLean_spec__0(x_1, x_23);
x_25 = l_String_intercalate(x_22, x_24);
x_26 = lean_string_append(x_21, x_25);
lean_dec_ref(x_25);
x_27 = lean_mk_io_user_error(x_26);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = l_Lean_Name_getRoot(x_2);
x_30 = 0;
x_31 = l_Lean_Name_toString(x_29, x_30);
x_32 = l_Lean_findOLean___closed__1;
x_33 = lean_string_append(x_32, x_31);
x_34 = l_Lean_findOLean___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_31);
x_37 = l_Lean_findOLean___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_31);
lean_dec_ref(x_31);
x_40 = l_Lean_findLean___closed__0;
x_41 = lean_string_append(x_39, x_40);
x_42 = l_Lean_findOLean___closed__5;
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at___Lean_findOLean_spec__0(x_1, x_43);
x_45 = l_String_intercalate(x_42, x_44);
x_46 = lean_string_append(x_41, x_45);
lean_dec_ref(x_45);
x_47 = lean_mk_io_user_error(x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_28);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_5);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_5, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_6, 0);
lean_inc(x_51);
lean_dec_ref(x_6);
lean_ctor_set(x_5, 0, x_51);
return x_5;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_5, 1);
lean_inc(x_52);
lean_dec(x_5);
x_53 = lean_ctor_get(x_6, 0);
lean_inc(x_53);
lean_dec_ref(x_6);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findLean(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_getSrcSearchPath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SRC_PATH", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_getSrcSearchPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("src", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_getSrcSearchPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_getSrcSearchPath___closed__0;
x_3 = lean_io_getenv(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_6 = x_3;
} else {
 lean_dec_ref(x_3);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_7 = x_43;
goto block_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
lean_dec_ref(x_4);
x_45 = l_System_SearchPath_parse(x_44);
lean_dec(x_44);
x_7 = x_45;
goto block_42;
}
block_42:
{
lean_object* x_8; 
x_8 = l_IO_appDir(x_5);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_getLibDir___closed__2;
x_12 = l_System_FilePath_join(x_10, x_11);
x_13 = l_Lean_getSrcSearchPath___closed__1;
x_14 = l_System_FilePath_join(x_12, x_13);
x_15 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_16 = l_System_FilePath_join(x_14, x_15);
x_17 = l_Lean_getSrcSearchPath___closed__2;
lean_inc_ref(x_16);
x_18 = l_System_FilePath_join(x_16, x_17);
x_19 = lean_box(0);
if (lean_is_scalar(x_6)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_6;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_appendTR___redArg(x_7, x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = l_Lean_getLibDir___closed__2;
x_26 = l_System_FilePath_join(x_23, x_25);
x_27 = l_Lean_getSrcSearchPath___closed__1;
x_28 = l_System_FilePath_join(x_26, x_27);
x_29 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_30 = l_System_FilePath_join(x_28, x_29);
x_31 = l_Lean_getSrcSearchPath___closed__2;
lean_inc_ref(x_30);
x_32 = l_System_FilePath_join(x_30, x_31);
x_33 = lean_box(0);
if (lean_is_scalar(x_6)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_6;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_List_appendTR___redArg(x_7, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_8);
if (x_38 == 0)
{
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_8, 0);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_moduleNameOfFileName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Name_str___override(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input file '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' must be contained in root directory (", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static uint32_t _init_l_Lean_moduleNameOfFileName___closed__3() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_pathSeparator;
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_moduleNameOfFileName___closed__3;
x_2 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_moduleNameOfFileName___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_moduleNameOfFileName___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_moduleNameOfFileName___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_moduleNameOfFileName___closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_realpath(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_34; lean_object* x_35; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_54; 
x_54 = lean_io_current_dir(x_6);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_34 = x_55;
x_35 = x_56;
goto block_53;
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_54);
if (x_57 == 0)
{
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_2, 0);
lean_inc(x_61);
lean_dec_ref(x_2);
x_34 = x_61;
x_35 = x_6;
goto block_53;
}
block_33:
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_5);
x_10 = l_System_FilePath_normalize(x_5);
x_11 = l_String_isPrefixOf(x_8, x_10);
lean_dec_ref(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lean_moduleNameOfFileName___closed__0;
x_13 = lean_string_append(x_12, x_5);
lean_dec(x_5);
x_14 = l_Lean_moduleNameOfFileName___closed__1;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_8);
lean_dec_ref(x_8);
x_17 = l_Lean_moduleNameOfFileName___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_mk_io_user_error(x_18);
if (lean_is_scalar(x_7)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_7;
 lean_ctor_set_tag(x_20, 1);
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_21 = lean_string_length(x_8);
lean_dec_ref(x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_string_utf8_byte_size(x_5);
lean_inc(x_23);
lean_inc(x_5);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Substring_nextn(x_24, x_21, x_22);
lean_dec_ref(x_24);
x_26 = lean_string_utf8_extract(x_5, x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
lean_dec(x_5);
x_27 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_28 = l_System_FilePath_withExtension(x_26, x_27);
x_29 = lean_box(0);
x_30 = l_System_FilePath_components(x_28);
x_31 = l_List_foldl___at___Lean_moduleNameOfFileName_spec__0(x_29, x_30);
if (lean_is_scalar(x_7)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_7;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
block_53:
{
lean_object* x_36; 
x_36 = l_Lean_realPathNormalized(x_34, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_moduleNameOfFileName___closed__4;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_string_utf8_byte_size(x_37);
lean_inc(x_41);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_moduleNameOfFileName___closed__5;
lean_inc(x_41);
x_44 = l_Substring_prevn(x_42, x_43, x_41);
lean_dec_ref(x_42);
lean_inc(x_37);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_41);
x_46 = l_Lean_moduleNameOfFileName___closed__7;
x_47 = l_Substring_beq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_string_append(x_37, x_39);
x_8 = x_48;
x_9 = x_38;
goto block_33;
}
else
{
x_8 = x_37;
x_9 = x_38;
goto block_33;
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_4);
if (x_62 == 0)
{
return x_4;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_4, 0);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_4);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_9);
lean_inc_ref(x_1);
x_12 = l_Lean_moduleNameOfFileName(x_1, x_11, x_6);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_free_object(x_4);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec_ref(x_12);
lean_inc_ref(x_3);
{
lean_object* _tmp_3 = x_10;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_5 = x_22;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
lean_inc_ref(x_1);
x_27 = l_Lean_moduleNameOfFileName(x_1, x_26, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_2);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec_ref(x_27);
lean_inc_ref(x_3);
{
lean_object* _tmp_3 = x_25;
lean_object* _tmp_4 = x_3;
lean_object* _tmp_5 = x_35;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_searchModuleNameOfFileName___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = l_Lean_searchModuleNameOfFileName___closed__0;
x_7 = l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___redArg(x_1, x_5, x_6, x_2, x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec_ref(x_9);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec_ref(x_9);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_searchModuleNameOfFileName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_findSysroot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_findSysroot___closed__1() {
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
static lean_object* _init_l_Lean_findSysroot___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--print-prefix", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_findSysroot___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_findSysroot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_findSysroot___closed__2;
x_2 = l_Lean_findSysroot___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_findSysroot___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_findSysroot___closed__0;
x_4 = lean_io_getenv(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_findSysroot___closed__1;
x_8 = l_Lean_findSysroot___closed__4;
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_findSysroot___closed__5;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_9);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_IO_Process_run(x_14, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0(x_17, x_18, x_10);
x_20 = l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1(x_17, x_19, x_18);
x_21 = lean_string_utf8_extract(x_17, x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_string_utf8_byte_size(x_22);
x_25 = l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0(x_22, x_24, x_10);
x_26 = l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1(x_22, x_25, x_24);
x_27 = lean_string_utf8_extract(x_22, x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
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
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec_ref(x_5);
lean_ctor_set(x_4, 0, x_35);
return x_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_dec(x_4);
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
lean_dec_ref(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___Lean_findSysroot_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___Lean_findSysroot_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_forEachModuleInDir___redArg___lam__2___closed__0 = _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_forEachModuleInDir___redArg___lam__2___closed__0);
l_Lean_forEachModuleInDir___redArg___lam__2___closed__1 = _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lean_forEachModuleInDir___redArg___lam__2___closed__1);
l_Lean_forEachModuleInDir___redArg___lam__2___closed__2 = _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__2();
lean_mark_persistent(l_Lean_forEachModuleInDir___redArg___lam__2___closed__2);
l_Lean_forEachModuleInDir___redArg___lam__2___closed__3 = _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__3();
lean_mark_persistent(l_Lean_forEachModuleInDir___redArg___lam__2___closed__3);
l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0 = _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0();
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0);
l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1 = _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1();
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1);
l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2 = _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2();
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2);
l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3 = _init_l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3();
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_SearchPath_findAllWithExt_spec__3_spec__3___redArg___closed__0);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
}l_Lean_getBuildDir___closed__0 = _init_l_Lean_getBuildDir___closed__0();
lean_mark_persistent(l_Lean_getBuildDir___closed__0);
l_Lean_getBuildDir___closed__1 = _init_l_Lean_getBuildDir___closed__1();
lean_mark_persistent(l_Lean_getBuildDir___closed__1);
l_Lean_getBuildDir___closed__2 = _init_l_Lean_getBuildDir___closed__2();
lean_mark_persistent(l_Lean_getBuildDir___closed__2);
l_Lean_getBuildDir___closed__3 = _init_l_Lean_getBuildDir___closed__3();
lean_mark_persistent(l_Lean_getBuildDir___closed__3);
l_Lean_getLibDir___closed__0 = _init_l_Lean_getLibDir___closed__0();
lean_mark_persistent(l_Lean_getLibDir___closed__0);
l_Lean_getLibDir___closed__1 = _init_l_Lean_getLibDir___closed__1();
l_Lean_getLibDir___closed__2 = _init_l_Lean_getLibDir___closed__2();
lean_mark_persistent(l_Lean_getLibDir___closed__2);
l_Lean_getLibDir___closed__3 = _init_l_Lean_getLibDir___closed__3();
lean_mark_persistent(l_Lean_getLibDir___closed__3);
l_Lean_addSearchPathFromEnv___closed__0 = _init_l_Lean_addSearchPathFromEnv___closed__0();
lean_mark_persistent(l_Lean_addSearchPathFromEnv___closed__0);
l_Lean_initSearchPath___closed__0 = _init_l_Lean_initSearchPath___closed__0();
lean_mark_persistent(l_Lean_initSearchPath___closed__0);
l_Lean_findOLean___closed__0 = _init_l_Lean_findOLean___closed__0();
lean_mark_persistent(l_Lean_findOLean___closed__0);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean_mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findOLean___closed__2 = _init_l_Lean_findOLean___closed__2();
lean_mark_persistent(l_Lean_findOLean___closed__2);
l_Lean_findOLean___closed__3 = _init_l_Lean_findOLean___closed__3();
lean_mark_persistent(l_Lean_findOLean___closed__3);
l_Lean_findOLean___closed__4 = _init_l_Lean_findOLean___closed__4();
lean_mark_persistent(l_Lean_findOLean___closed__4);
l_Lean_findOLean___closed__5 = _init_l_Lean_findOLean___closed__5();
lean_mark_persistent(l_Lean_findOLean___closed__5);
l_Lean_findLean___closed__0 = _init_l_Lean_findLean___closed__0();
lean_mark_persistent(l_Lean_findLean___closed__0);
l_Lean_getSrcSearchPath___closed__0 = _init_l_Lean_getSrcSearchPath___closed__0();
lean_mark_persistent(l_Lean_getSrcSearchPath___closed__0);
l_Lean_getSrcSearchPath___closed__1 = _init_l_Lean_getSrcSearchPath___closed__1();
lean_mark_persistent(l_Lean_getSrcSearchPath___closed__1);
l_Lean_getSrcSearchPath___closed__2 = _init_l_Lean_getSrcSearchPath___closed__2();
lean_mark_persistent(l_Lean_getSrcSearchPath___closed__2);
l_Lean_moduleNameOfFileName___closed__0 = _init_l_Lean_moduleNameOfFileName___closed__0();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__0);
l_Lean_moduleNameOfFileName___closed__1 = _init_l_Lean_moduleNameOfFileName___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__1);
l_Lean_moduleNameOfFileName___closed__2 = _init_l_Lean_moduleNameOfFileName___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__2);
l_Lean_moduleNameOfFileName___closed__3 = _init_l_Lean_moduleNameOfFileName___closed__3();
l_Lean_moduleNameOfFileName___closed__4 = _init_l_Lean_moduleNameOfFileName___closed__4();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__4);
l_Lean_moduleNameOfFileName___closed__5 = _init_l_Lean_moduleNameOfFileName___closed__5();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__5);
l_Lean_moduleNameOfFileName___closed__6 = _init_l_Lean_moduleNameOfFileName___closed__6();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__6);
l_Lean_moduleNameOfFileName___closed__7 = _init_l_Lean_moduleNameOfFileName___closed__7();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__7);
l_Lean_searchModuleNameOfFileName___closed__0 = _init_l_Lean_searchModuleNameOfFileName___closed__0();
lean_mark_persistent(l_Lean_searchModuleNameOfFileName___closed__0);
l_Lean_findSysroot___closed__0 = _init_l_Lean_findSysroot___closed__0();
lean_mark_persistent(l_Lean_findSysroot___closed__0);
l_Lean_findSysroot___closed__1 = _init_l_Lean_findSysroot___closed__1();
lean_mark_persistent(l_Lean_findSysroot___closed__1);
l_Lean_findSysroot___closed__2 = _init_l_Lean_findSysroot___closed__2();
lean_mark_persistent(l_Lean_findSysroot___closed__2);
l_Lean_findSysroot___closed__3 = _init_l_Lean_findSysroot___closed__3();
lean_mark_persistent(l_Lean_findSysroot___closed__3);
l_Lean_findSysroot___closed__4 = _init_l_Lean_findSysroot___closed__4();
lean_mark_persistent(l_Lean_findSysroot___closed__4);
l_Lean_findSysroot___closed__5 = _init_l_Lean_findSysroot___closed__5();
lean_mark_persistent(l_Lean_findSysroot___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
