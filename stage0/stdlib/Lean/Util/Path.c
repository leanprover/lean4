// Lean compiler output
// Module: Lean.Util.Path
// Imports: public import Init.System.IO import Init.Data.ToString.Name import Init.Data.String.TakeDrop
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
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___closed__3;
LEAN_EXPORT lean_object* lean_init_search_path();
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__1;
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static uint8_t l_Lean_getLibDir___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*);
static lean_object* l_Lean_findLean___closed__0;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addSearchPathFromEnv___closed__0;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_SearchPath_parse(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
static lean_object* l_Lean_findSysroot___closed__0;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__2;
lean_object* lean_io_getenv(lean_object*);
static lean_object* l_Lean_findOLean___closed__4;
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*);
lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_findSysroot___closed__1;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__1;
static lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__3;
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__0;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_appDir();
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath();
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__0;
lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__3;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getLibDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3;
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__0(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object*, lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
static lean_object* l_Lean_getLibDir___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___closed__5;
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuildDir();
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__1;
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchPathRef;
static lean_object* l_Lean_findOLean___closed__5;
static lean_object* l_Lean_findSysroot___closed__4;
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* lean_io_realpath(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__2;
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__0;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_current_dir();
static lean_object* l_Lean_findSysroot___closed__2;
static lean_object* l_Lean_getLibDir___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_searchModuleNameOfFileName___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir(lean_object*);
static lean_object* l_Lean_findOLean___closed__0;
lean_object* l_IO_Process_run(lean_object*, lean_object*);
static lean_object* l_Lean_getSrcSearchPath___closed__0;
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___closed__1;
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3(lean_object* x_1) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_System_FilePath_isDir(x_1);
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_forEachModuleInDir___redArg___lam__3(x_1);
lean_dec_ref(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_forEachModuleInDir___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
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
x_16 = l_Option_instBEq_beq___redArg(x_13, x_14, x_15);
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_12);
x_14 = l_Lean_forEachModuleInDir___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_13);
return x_14;
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
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_forEachModuleInDir___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_System_FilePath_normalize(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_realPathNormalized___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_realPathNormalized(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(lean_object* x_1) {
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
x_3 = lean_unsigned_to_nat(46u);
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
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go(x_1, x_3);
x_6 = l_System_FilePath_join(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_2);
x_7 = l___private_Lean_Util_Path_0__Lean_modToFilePath_go___closed__3;
x_8 = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_7);
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
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
lean_inc_ref(x_1);
lean_inc(x_7);
x_13 = l_System_FilePath_join(x_7, x_1);
x_14 = l_System_FilePath_isDir(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_System_FilePath_addExtension(x_13, x_2);
x_16 = l_System_FilePath_pathExists(x_15);
lean_dec_ref(x_15);
if (x_16 == 0)
{
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
}
else
{
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = 0;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_List_findM_x3f___at___00Lean_SearchPath_findWithExt_spec__0(x_7, x_2, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_3);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_19 = x_9;
} else {
 lean_dec_ref(x_9);
 x_19 = lean_box(0);
}
x_20 = l_Lean_modToFilePath(x_18, x_3, x_2);
lean_dec(x_18);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
x_13 = l_System_FilePath_pathExists(x_12);
if (x_13 == 0)
{
lean_free_object(x_9);
lean_dec_ref(x_11);
x_5 = lean_box(0);
goto block_8;
}
else
{
return x_9;
}
}
else
{
lean_free_object(x_9);
lean_dec(x_11);
x_5 = lean_box(0);
goto block_8;
}
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = l_System_FilePath_pathExists(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_14);
x_5 = lean_box(0);
goto block_8;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
return x_17;
}
}
else
{
lean_dec(x_14);
x_5 = lean_box(0);
goto block_8;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findModuleWithExt(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_12);
x_13 = l_System_FilePath_extension(x_12);
lean_inc_ref(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = l_Option_instBEq_beq___at___00Lean_SearchPath_findAllWithExt_spec__0(x_13, x_14);
lean_dec_ref(x_14);
lean_dec(x_13);
if (x_15 == 0)
{
lean_dec(x_12);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0(x_4, x_2);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_System_FilePath_isDir(x_6);
if (x_8 == 0)
{
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_8);
x_11 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_System_FilePath_walkDir(x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_13);
x_20 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0;
x_21 = lean_nat_dec_lt(x_18, x_19);
if (x_21 == 0)
{
lean_dec(x_13);
x_14 = x_20;
goto block_17;
}
else
{
uint8_t x_22; 
x_22 = lean_nat_dec_le(x_19, x_19);
if (x_22 == 0)
{
if (x_21 == 0)
{
lean_dec(x_13);
x_14 = x_20;
goto block_17;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_19);
lean_inc_ref(x_1);
x_25 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(x_1, x_13, x_23, x_24, x_20);
lean_dec(x_13);
x_14 = x_25;
goto block_17;
}
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_19);
lean_inc_ref(x_1);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SearchPath_findAllWithExt_spec__1(x_1, x_13, x_26, x_27, x_20);
lean_dec(x_13);
x_14 = x_28;
goto block_17;
}
}
block_17:
{
lean_object* x_15; 
x_15 = l_Array_append___redArg(x_3, x_14);
lean_dec_ref(x_14);
x_2 = x_7;
x_3 = x_15;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0;
x_5 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(x_2, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SearchPath_findAllWithExt(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg(x_1, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
return x_2;
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
x_3 = lean_unsigned_to_nat(22u);
x_4 = l_Lean_getBuildDir___closed__1;
x_5 = l_Lean_getBuildDir___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir() {
_start:
{
lean_object* x_2; 
x_2 = l_IO_appDir();
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_System_FilePath_parent(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_getBuildDir___closed__3;
x_7 = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_6);
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
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_System_FilePath_parent(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_getBuildDir___closed__3;
x_12 = l_panic___at___00__private_Lean_Util_Path_0__Lean_modToFilePath_go_spec__0(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuildDir___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getBuildDir();
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_getLibDir(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_11; 
x_11 = l_Lean_getLibDir___closed__1;
if (x_11 == 0)
{
x_3 = x_1;
x_4 = lean_box(0);
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
x_4 = lean_box(0);
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_getLibDir___closed__0;
x_6 = l_System_FilePath_join(x_3, x_5);
x_7 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_8 = l_System_FilePath_join(x_6, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getLibDir(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_getLibDir(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getBuiltinSearchPath(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_addSearchPathFromEnv___closed__0;
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = l_System_SearchPath_parse(x_7);
x_9 = l_List_appendTR___redArg(x_8, x_1);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_System_SearchPath_parse(x_10);
x_12 = l_List_appendTR___redArg(x_11, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_addSearchPathFromEnv(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getBuiltinSearchPath(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_addSearchPathFromEnv(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_List_appendTR___redArg(x_2, x_8);
x_10 = l_Lean_searchPathRef;
x_11 = lean_st_ref_set(x_10, x_9);
lean_ctor_set(x_6, 0, x_11);
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = l_List_appendTR___redArg(x_2, x_12);
x_14 = l_Lean_searchPathRef;
x_15 = lean_st_ref_set(x_14, x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initSearchPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initSearchPath(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lean_init_search_path() {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getBuildDir();
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_initSearchPath(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Path_0__Lean_initSearchPathInternal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_search_path();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_findOLean_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l_Lean_searchPathRef;
x_4 = lean_st_ref_get(x_3);
x_5 = l_Lean_findOLean___closed__0;
lean_inc(x_1);
lean_inc(x_4);
x_6 = l_Lean_SearchPath_findWithExt(x_4, x_5, x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_10 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
x_11 = 0;
x_12 = l_Lean_Name_toString(x_10, x_11);
x_13 = l_Lean_findOLean___closed__1;
x_14 = lean_string_append(x_13, x_12);
x_15 = l_Lean_findOLean___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_16, x_12);
x_18 = l_Lean_findOLean___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_12);
lean_dec_ref(x_12);
x_21 = l_Lean_findOLean___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = l_Lean_findOLean___closed__5;
x_24 = lean_box(0);
x_25 = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(x_4, x_24);
x_26 = l_String_intercalate(x_23, x_25);
x_27 = lean_string_append(x_22, x_26);
lean_dec_ref(x_26);
x_28 = lean_mk_io_user_error(x_27);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_29);
x_32 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
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
x_47 = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(x_4, x_46);
x_48 = l_String_intercalate(x_45, x_47);
x_49 = lean_string_append(x_44, x_48);
lean_dec_ref(x_48);
x_50 = lean_mk_io_user_error(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_findOLean(x_1);
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
LEAN_EXPORT lean_object* l_Lean_findLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_4, x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_9 = l_Lean_Name_getRoot(x_2);
lean_dec(x_2);
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
x_24 = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(x_1, x_23);
x_25 = l_String_intercalate(x_22, x_24);
x_26 = lean_string_append(x_21, x_25);
lean_dec_ref(x_25);
x_27 = lean_mk_io_user_error(x_26);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_27);
return x_5;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_28);
x_31 = l_Lean_Name_getRoot(x_2);
lean_dec(x_2);
x_32 = 0;
x_33 = l_Lean_Name_toString(x_31, x_32);
x_34 = l_Lean_findOLean___closed__1;
x_35 = lean_string_append(x_34, x_33);
x_36 = l_Lean_findOLean___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_33);
x_39 = l_Lean_findOLean___closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_33);
lean_dec_ref(x_33);
x_42 = l_Lean_findLean___closed__0;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Lean_findOLean___closed__5;
x_45 = lean_box(0);
x_46 = l_List_mapTR_loop___at___00Lean_findOLean_spec__0(x_1, x_45);
x_47 = l_String_intercalate(x_44, x_46);
x_48 = lean_string_append(x_43, x_47);
lean_dec_ref(x_47);
x_49 = lean_mk_io_user_error(x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findLean___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findLean(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getSrcSearchPath___closed__0;
x_3 = lean_io_getenv(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_38; 
x_38 = lean_box(0);
x_4 = x_38;
goto block_37;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec_ref(x_3);
x_40 = l_System_SearchPath_parse(x_39);
x_4 = x_40;
goto block_37;
}
block_37:
{
lean_object* x_5; 
x_5 = l_IO_appDir();
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_getLibDir___closed__2;
x_9 = l_System_FilePath_join(x_7, x_8);
x_10 = l_Lean_getSrcSearchPath___closed__1;
x_11 = l_System_FilePath_join(x_9, x_10);
x_12 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_13 = l_System_FilePath_join(x_11, x_12);
x_14 = l_Lean_getSrcSearchPath___closed__2;
lean_inc_ref(x_13);
x_15 = l_System_FilePath_join(x_13, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_List_appendTR___redArg(x_4, x_18);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = l_Lean_getLibDir___closed__2;
x_22 = l_System_FilePath_join(x_20, x_21);
x_23 = l_Lean_getSrcSearchPath___closed__1;
x_24 = l_System_FilePath_join(x_22, x_23);
x_25 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__1;
x_26 = l_System_FilePath_join(x_24, x_25);
x_27 = l_Lean_getSrcSearchPath___closed__2;
lean_inc_ref(x_26);
x_28 = l_System_FilePath_join(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_List_appendTR___redArg(x_4, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_4);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
return x_5;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_5, 0);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getSrcSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_getSrcSearchPath();
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__3() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparator;
x_2 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_moduleNameOfFileName___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_realpath(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_19; lean_object* x_20; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_44; lean_object* x_45; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_59; 
x_59 = lean_io_current_dir();
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_44 = x_60;
x_45 = lean_box(0);
goto block_58;
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
lean_dec_ref(x_2);
x_44 = x_64;
x_45 = lean_box(0);
goto block_58;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_moduleNameOfFileName___closed__0;
x_10 = lean_string_append(x_9, x_5);
lean_dec(x_5);
x_11 = l_Lean_moduleNameOfFileName___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_8);
lean_dec_ref(x_8);
x_14 = l_Lean_moduleNameOfFileName___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_mk_io_user_error(x_15);
if (lean_is_scalar(x_6)) {
 x_17 = lean_alloc_ctor(1, 1, 0);
} else {
 x_17 = x_6;
 lean_ctor_set_tag(x_17, 1);
}
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
block_38:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_5);
x_21 = l_System_FilePath_normalize(x_5);
x_22 = lean_string_utf8_byte_size(x_21);
x_23 = lean_string_utf8_byte_size(x_19);
x_24 = lean_nat_dec_le(x_23, x_22);
if (x_24 == 0)
{
lean_dec_ref(x_21);
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_string_memcmp(x_21, x_19, x_25, x_25, x_23);
lean_dec_ref(x_21);
if (x_26 == 0)
{
x_7 = lean_box(0);
x_8 = x_19;
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_6);
x_27 = lean_string_length(x_19);
lean_dec_ref(x_19);
x_28 = lean_string_utf8_byte_size(x_5);
lean_inc(x_5);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_String_Slice_Pos_nextn(x_29, x_25, x_27);
lean_dec_ref(x_29);
x_31 = lean_string_utf8_extract(x_5, x_30, x_28);
lean_dec(x_30);
lean_dec(x_5);
x_32 = l_Lean_forEachModuleInDir___redArg___lam__2___closed__3;
x_33 = l_System_FilePath_withExtension(x_31, x_32);
x_34 = lean_box(0);
x_35 = l_System_FilePath_components(x_33);
x_36 = l_List_foldl___at___00Lean_moduleNameOfFileName_spec__0(x_34, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
block_43:
{
lean_object* x_42; 
x_42 = lean_string_append(x_39, x_40);
lean_dec_ref(x_40);
x_19 = x_42;
x_20 = lean_box(0);
goto block_38;
}
block_58:
{
lean_object* x_46; 
x_46 = l_Lean_realPathNormalized(x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_moduleNameOfFileName___closed__3;
x_49 = lean_string_utf8_byte_size(x_47);
x_50 = l_Lean_moduleNameOfFileName___closed__4;
x_51 = lean_nat_dec_le(x_50, x_49);
if (x_51 == 0)
{
x_39 = x_47;
x_40 = x_48;
x_41 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_sub(x_49, x_50);
x_54 = lean_string_memcmp(x_47, x_48, x_53, x_52, x_50);
lean_dec(x_53);
if (x_54 == 0)
{
x_39 = x_47;
x_40 = x_48;
x_41 = lean_box(0);
goto block_43;
}
else
{
x_19 = x_47;
x_20 = lean_box(0);
goto block_38;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
return x_46;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_4);
if (x_65 == 0)
{
return x_4;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_4, 0);
lean_inc(x_66);
lean_dec(x_4);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_moduleNameOfFileName(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_5);
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
x_12 = l_Lean_moduleNameOfFileName(x_1, x_11);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_4);
return x_20;
}
}
else
{
lean_dec_ref(x_12);
lean_free_object(x_4);
lean_inc_ref(x_3);
{
lean_object* _tmp_3 = x_10;
lean_object* _tmp_4 = x_3;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
lean_inc_ref(x_1);
x_25 = l_Lean_moduleNameOfFileName(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_23);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_dec_ref(x_25);
lean_inc_ref(x_3);
{
lean_object* _tmp_3 = x_23;
lean_object* _tmp_4 = x_3;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = l_Lean_searchModuleNameOfFileName___closed__0;
x_7 = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(x_1, x_5, x_6, x_2, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_searchModuleNameOfFileName(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___redArg(x_1, x_2, x_3, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___00Lean_searchModuleNameOfFileName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_9;
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
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_findSysroot___closed__0;
x_4 = lean_io_getenv(x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 0);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_8 = l_Lean_findSysroot___closed__1;
x_9 = l_Lean_findSysroot___closed__4;
x_10 = lean_box(0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_findSysroot___closed__5;
x_13 = 1;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_9);
lean_ctor_set(x_15, 3, x_10);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
x_16 = l_IO_Process_run(x_15, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_string_utf8_byte_size(x_18);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_11);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_String_Slice_trimAscii(x_20);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec_ref(x_21);
x_25 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_String_Slice_trimAscii(x_28);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = lean_string_utf8_extract(x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_findSysroot(x_1);
return x_3;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Path(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
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
l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___00Lean_SearchPath_findAllWithExt_spec__2___redArg___closed__0);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_Path_2007882598____hygCtx___hyg_2_();
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
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__3);
l_Lean_moduleNameOfFileName___closed__4 = _init_l_Lean_moduleNameOfFileName___closed__4();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__4);
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
