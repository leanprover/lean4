// Lean compiler output
// Module: Lean.Util.Path
// Imports: Init.System.IO Init.Data.List.Control
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRoot___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_endsWith(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__3___closed__1;
LEAN_EXPORT lean_object* lean_init_search_path(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_getLibDir___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2;
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_modToFilePath_go___spec__1(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
static lean_object* l_Lean_moduleExists_go___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRoot(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__3;
lean_object* l_System_SearchPath_parse(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
static lean_object* l_Lean_modToFilePath_go___closed__3;
static lean_object* l_Lean_findSysroot___lambda__1___closed__2;
static lean_object* l_Lean_SearchPath_findAllWithExt___closed__1;
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_getLibDir___closed__4;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__4;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_DirEntry_path(lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath_go___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_readDir___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1;
static lean_object* l_Lean_findSysroot___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1;
static lean_object* l_Lean_findOLean___closed__9;
static lean_object* l_Lean_findOLean___closed__6;
static lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1;
static lean_object* l_Lean_findOLean___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
lean_object* l_List_map___at_System_SearchPath_toString___spec__1(lean_object*);
static lean_object* l_Lean_findOLean___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_moduleExists_go(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__7;
static lean_object* l_Lean_modToFilePath_go___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__2;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lean_modToFilePath_go___closed__2;
extern lean_object* l_IO_instInhabitedError;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initSearchPath___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_1117_(lean_object*);
static lean_object* l_Lean_getLibDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_moduleExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__1;
extern uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__3;
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__4;
static lean_object* l_Lean_findSysroot___lambda__1___closed__1;
LEAN_EXPORT lean_object* lean_get_prefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleExists_go___closed__2;
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchPathRef;
static lean_object* l_Lean_findOLean___closed__5;
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__8;
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleExists_go___closed__1;
extern lean_object* l_System_instInhabitedFilePath;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_Lean_searchModuleNameOfFileName___closed__1;
static lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_moduleExists_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleExists(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3___boxed(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_io_read_dir(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_current_dir(lean_object*);
static uint8_t l_Lean_getLibDir___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_getLibDir___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* lean_get_libdir(lean_object*, lean_object*);
static lean_object* l_Lean_SearchPath_findModuleWithExt___closed__1;
lean_object* l_IO_Process_run(lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_moduleExists_go___spec__2___closed__1;
static lean_object* l_Lean_modToFilePath_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1;
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Name_append(x_1, x_3);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_8 = l_System_FilePath_extension(x_1);
x_9 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2;
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
x_15 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___boxed), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_19 = l_System_FilePath_withExtension(x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_19);
x_22 = lean_apply_1(x_5, x_21);
x_23 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_23, 0, x_2);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_22, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_box(0);
x_27 = l_Lean_Name_str___override(x_26, x_25);
x_28 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__4), 3, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_5);
lean_inc(x_2);
x_29 = l_Lean_forEachModuleInDir___rarg(x_2, x_6, x_1, x_28);
x_30 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3___boxed), 2, 1);
lean_closure_set(x_30, 0, x_2);
x_31 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_10);
return x_13;
}
else
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_16, x_14);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_8, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
x_14 = lean_array_uget(x_6, x_8);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_IO_FS_DirEntry_path(x_14);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_16);
lean_inc(x_5);
x_18 = lean_apply_2(x_5, lean_box(0), x_17);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_4);
lean_closure_set(x_19, 3, x_14);
lean_closure_set(x_19, 4, x_3);
lean_closure_set(x_19, 5, x_2);
lean_inc(x_4);
x_20 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_19);
x_21 = lean_box_usize(x_8);
x_22 = lean_box_usize(x_7);
x_23 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6___boxed), 9, 8);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_closure_set(x_23, 6, x_6);
lean_closure_set(x_23, 7, x_22);
x_24 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_20, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = lean_box(0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg(x_1, x_2, x_3, x_4, x_2, x_5, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_System_FilePath_readDir___boxed), 2, 1);
lean_closure_set(x_6, 0, x_3);
lean_inc(x_2);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___rarg___lambda__2), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_forEachModuleInDir___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__6(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_12 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_forEachModuleInDir___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_forEachModuleInDir___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
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
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_modToFilePath_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_instInhabitedFilePath;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Util.Path", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.modToFilePath.go", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed import", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_modToFilePath_go___closed__1;
x_2 = l_Lean_modToFilePath_go___closed__2;
x_3 = lean_unsigned_to_nat(41u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_modToFilePath_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_inc(x_1);
return x_1;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_modToFilePath_go(x_1, x_3);
x_6 = l_System_FilePath_join(x_5, x_4);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = l_Lean_modToFilePath_go___closed__4;
x_8 = l_panic___at_Lean_modToFilePath_go___spec__1(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_modToFilePath_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_modToFilePath_go(x_1, x_2);
x_5 = l_System_FilePath_addExtension(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_modToFilePath(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_panic___at_Lean_moduleExists_go___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_IO_instInhabitedError;
x_2 = lean_alloc_closure((void*)(l_EStateM_instInhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_moduleExists_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_panic___at_Lean_moduleExists_go___spec__2___closed__1;
x_4 = lean_panic_fn(x_3, x_1);
x_5 = lean_apply_1(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_7 = l_Lean_modToFilePath(x_1, x_2, x_6);
x_8 = lean_io_read_dir(x_7, x_5);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_18 = l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1(x_3, x_10, x_16, x_17);
lean_dec(x_10);
x_19 = lean_box(x_18);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_array_get_size(x_20);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1(x_3, x_20, x_28, x_29);
lean_dec(x_20);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_moduleExists_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleExists_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.moduleExists.go", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleExists_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_modToFilePath_go___closed__1;
x_2 = l_Lean_moduleExists_go___closed__2;
x_3 = lean_unsigned_to_nat(58u);
x_4 = lean_unsigned_to_nat(15u);
x_5 = l_Lean_modToFilePath_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_System_FilePath_pathExists(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_33; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec(x_3);
x_33 = l_String_isEmpty(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_35 = lean_string_append(x_34, x_11);
lean_dec(x_11);
x_36 = l_Lean_moduleExists_go___closed__1;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_2);
x_39 = lean_string_append(x_38, x_34);
x_12 = x_39;
goto block_32;
}
else
{
x_12 = x_11;
goto block_32;
}
block_32:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
lean_inc(x_10);
x_14 = l_Lean_moduleExists_go(x_1, x_13, x_10, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_box(0);
x_27 = l_Lean_moduleExists_go___lambda__1(x_1, x_10, x_12, x_26, x_25);
lean_dec(x_12);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_12);
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_3);
x_40 = l_Lean_moduleExists_go___closed__3;
x_41 = l_panic___at_Lean_moduleExists_go___spec__2(x_40, x_4);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_moduleExists_go___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_moduleExists_go___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleExists_go(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleExists_go(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleExists(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_string_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_System_FilePath_join(x_1, x_2);
x_7 = l_System_FilePath_isDir(x_6, x_5);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_12 = lean_string_append(x_11, x_2);
lean_dec(x_2);
x_13 = l_Lean_moduleExists_go___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_3);
x_16 = lean_string_append(x_15, x_11);
x_17 = lean_io_read_dir(x_1, x_10);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
size_t x_25; size_t x_26; uint8_t x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_27 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1(x_16, x_19, x_25, x_26);
lean_dec(x_19);
lean_dec(x_16);
x_28 = lean_box(x_27);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_16);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
size_t x_37; size_t x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1(x_16, x_29, x_37, x_38);
lean_dec(x_29);
lean_dec(x_16);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_30);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_16);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_17);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_7, 1);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_io_read_dir(x_1, x_46);
lean_dec(x_1);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_array_get_size(x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_lt(x_51, x_50);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_2);
x_53 = 0;
x_54 = lean_box(x_53);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; lean_object* x_58; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_57 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2(x_2, x_49, x_55, x_56);
lean_dec(x_49);
lean_dec(x_2);
x_58 = lean_box(x_57);
lean_ctor_set(x_47, 0, x_58);
return x_47;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_lt(x_62, x_61);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_2);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
else
{
size_t x_67; size_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_67 = 0;
x_68 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_69 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2(x_2, x_59, x_67, x_68);
lean_dec(x_59);
lean_dec(x_2);
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_60);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_47);
if (x_72 == 0)
{
return x_47;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_47, 0);
x_74 = lean_ctor_get(x_47, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_47);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_System_FilePath_isDir(x_7, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_3 = x_8;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
lean_inc(x_2);
lean_inc(x_7);
x_16 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1(x_7, x_2, x_1, x_15, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_7);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_3 = x_8;
x_4 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_7);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRoot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(x_2, x_3, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_SearchPath_findRoot___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findRoot___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findRoot(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = 0;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(x_2, x_7, x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = l_Lean_modToFilePath(x_19, x_3, x_2);
lean_dec(x_19);
lean_ctor_set(x_9, 0, x_20);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = l_Lean_modToFilePath(x_21, x_3, x_2);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_26 = x_9;
} else {
 lean_dec_ref(x_9);
 x_26 = lean_box(0);
}
x_27 = l_Lean_modToFilePath(x_25, x_3, x_2);
lean_dec(x_25);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_SearchPath_findModuleWithExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_SearchPath_findModuleWithExt___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = 0;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(x_2, x_7, x_1, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_SearchPath_findModuleWithExt___closed__1;
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, x_12, x_10);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_3);
x_16 = l_Lean_moduleExists_go(x_15, x_2, x_3, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
lean_dec(x_15);
lean_dec(x_3);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_11, x_20, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
x_24 = l_Lean_modToFilePath(x_15, x_3, x_2);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_24);
lean_ctor_set(x_16, 0, x_9);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = l_Lean_modToFilePath(x_15, x_3, x_2);
lean_dec(x_15);
lean_ctor_set(x_9, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_free_object(x_9);
lean_dec(x_15);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
lean_dec(x_9);
lean_inc(x_3);
x_33 = l_Lean_moduleExists_go(x_32, x_2, x_3, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_32);
lean_dec(x_3);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = lean_apply_2(x_11, x_37, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_40 = x_33;
} else {
 lean_dec_ref(x_33);
 x_40 = lean_box(0);
}
x_41 = l_Lean_modToFilePath(x_32, x_3, x_2);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
lean_dec(x_3);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_8);
if (x_48 == 0)
{
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 0);
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_8);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SearchPath_findModuleWithExt___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findModuleWithExt(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
x_8 = l_System_FilePath_extension(x_7);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at_Lean_forEachModuleInDir___spec__1(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_3);
x_9 = l_System_FilePath_isDir(x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_3 = x_8;
x_5 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1;
x_16 = l_System_FilePath_walkDir(x_7, x_15, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_dec(x_17);
x_22 = l_Array_append___rarg(x_4, x_2);
x_3 = x_8;
x_4 = x_22;
x_5 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_19, x_19);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_19);
lean_dec(x_17);
x_25 = l_Array_append___rarg(x_4, x_2);
x_3 = x_8;
x_4 = x_25;
x_5 = x_18;
goto _start;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1(x_1, x_17, x_27, x_28, x_2);
lean_dec(x_17);
x_30 = l_Array_append___rarg(x_4, x_29);
lean_dec(x_29);
x_3 = x_8;
x_4 = x_30;
x_5 = x_18;
goto _start;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
}
static lean_object* _init_l_Lean_SearchPath_findAllWithExt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_SearchPath_findAllWithExt___closed__1;
x_5 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2(x_2, x_4, x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_1117_(lean_object* x_1) {
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
static lean_object* _init_l_Lean_getBuildDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_getBuildDir___closed__1;
x_2 = l_Lean_getBuildDir___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_getBuildDir___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_getBuildDir___closed__4;
x_7 = l_panic___at_Lean_modToFilePath_go___spec__1(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
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
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_getBuildDir___closed__4;
x_13 = l_panic___at_Lean_modToFilePath_go___spec__1(x_12);
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
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_getLibDir___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_getLibDir___lambda__1___closed__1;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1;
x_7 = l_System_FilePath_join(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getLibDir___lambda__1___boxed), 3, 0);
return x_1;
}
}
static uint8_t _init_l_Lean_getLibDir___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_stage0(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("..", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__4() {
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
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_getLibDir___closed__1;
x_4 = l_Lean_getLibDir___closed__2;
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_3(x_3, x_1, x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_getLibDir___closed__3;
x_8 = l_System_FilePath_join(x_1, x_7);
x_9 = l_Lean_getLibDir___closed__4;
x_10 = l_System_FilePath_join(x_8, x_9);
x_11 = lean_box(0);
x_12 = lean_apply_3(x_3, x_10, x_11, x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getLibDir___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_libdir(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
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
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_addSearchPathFromEnv___closed__1() {
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
x_3 = l_Lean_addSearchPathFromEnv___closed__1;
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
lean_dec(x_5);
x_13 = l_System_SearchPath_parse(x_12);
lean_dec(x_12);
x_14 = l_List_appendTR___rarg(x_13, x_1);
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
lean_dec(x_5);
x_17 = l_System_SearchPath_parse(x_16);
lean_dec(x_16);
x_18 = l_List_appendTR___rarg(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
}
}
static lean_object* _init_l_Lean_initSearchPath___closed__1() {
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
lean_object* x_4; 
x_4 = l_Lean_getBuiltinSearchPath(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_addSearchPathFromEnv(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_List_appendTR___rarg(x_2, x_8);
x_11 = l_Lean_initSearchPath___closed__1;
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
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
lean_dec(x_2);
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
static lean_object* _init_l_Lean_findOLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown module prefix '", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n\nNo directory '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' or file '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".olean' in the search path entries:\n", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("object file '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' of module ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" does not exist", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lean_initSearchPath___closed__1;
x_5 = lean_st_ref_get(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Name_getRoot(x_1);
x_9 = 0;
x_10 = l_Lean_Name_toString(x_8, x_9);
x_11 = l_Lean_findOLean___closed__1;
lean_inc(x_6);
lean_inc(x_10);
x_12 = l_List_findM_x3f___at_Lean_SearchPath_findRoot___spec__3(x_11, x_10, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_findOLean___closed__2;
x_17 = lean_string_append(x_16, x_10);
x_18 = l_Lean_findOLean___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_10);
x_21 = l_Lean_findOLean___closed__4;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_10);
lean_dec(x_10);
x_24 = l_Lean_findOLean___closed__5;
x_25 = lean_string_append(x_23, x_24);
x_26 = l_List_map___at_System_SearchPath_toString___spec__1(x_6);
x_27 = l_Lean_findOLean___closed__6;
x_28 = l_String_intercalate(x_27, x_26);
x_29 = lean_string_append(x_25, x_28);
lean_dec(x_28);
x_30 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_32);
return x_12;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = l_Lean_findOLean___closed__2;
x_35 = lean_string_append(x_34, x_10);
x_36 = l_Lean_findOLean___closed__3;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_string_append(x_37, x_10);
x_39 = l_Lean_findOLean___closed__4;
x_40 = lean_string_append(x_38, x_39);
x_41 = lean_string_append(x_40, x_10);
lean_dec(x_10);
x_42 = l_Lean_findOLean___closed__5;
x_43 = lean_string_append(x_41, x_42);
x_44 = l_List_map___at_System_SearchPath_toString___spec__1(x_6);
x_45 = l_Lean_findOLean___closed__6;
x_46 = l_String_intercalate(x_45, x_44);
x_47 = lean_string_append(x_43, x_46);
lean_dec(x_46);
x_48 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_33);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_6);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_dec(x_12);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
lean_inc(x_1);
x_55 = l_Lean_modToFilePath(x_54, x_1, x_11);
lean_inc(x_1);
x_56 = l_Lean_moduleExists_go(x_54, x_11, x_1, x_52);
lean_dec(x_54);
if (lean_obj_tag(x_56) == 0)
{
if (x_2 == 0)
{
uint8_t x_57; 
lean_free_object(x_13);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_56);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_56, 0);
lean_dec(x_64);
x_65 = l_Lean_findOLean___closed__7;
x_66 = lean_string_append(x_65, x_55);
lean_dec(x_55);
x_67 = l_Lean_findOLean___closed__8;
x_68 = lean_string_append(x_66, x_67);
x_69 = 1;
x_70 = l_Lean_Name_toString(x_1, x_69);
x_71 = lean_string_append(x_68, x_70);
lean_dec(x_70);
x_72 = l_Lean_findOLean___closed__9;
x_73 = lean_string_append(x_71, x_72);
lean_ctor_set_tag(x_13, 18);
lean_ctor_set(x_13, 0, x_73);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_13);
return x_56;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
lean_dec(x_56);
x_75 = l_Lean_findOLean___closed__7;
x_76 = lean_string_append(x_75, x_55);
lean_dec(x_55);
x_77 = l_Lean_findOLean___closed__8;
x_78 = lean_string_append(x_76, x_77);
x_79 = 1;
x_80 = l_Lean_Name_toString(x_1, x_79);
x_81 = lean_string_append(x_78, x_80);
lean_dec(x_80);
x_82 = l_Lean_findOLean___closed__9;
x_83 = lean_string_append(x_81, x_82);
lean_ctor_set_tag(x_13, 18);
lean_ctor_set(x_13, 0, x_83);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_13);
lean_ctor_set(x_84, 1, x_74);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_free_object(x_13);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_56);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_56, 0);
lean_dec(x_86);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_56, 1);
lean_inc(x_87);
lean_dec(x_56);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_55);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_55);
lean_free_object(x_13);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_56);
if (x_89 == 0)
{
return x_56;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_56, 0);
x_91 = lean_ctor_get(x_56, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_56);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_13, 0);
lean_inc(x_93);
lean_dec(x_13);
lean_inc(x_1);
x_94 = l_Lean_modToFilePath(x_93, x_1, x_11);
lean_inc(x_1);
x_95 = l_Lean_moduleExists_go(x_93, x_11, x_1, x_52);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 0)
{
if (x_2 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
else
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
x_103 = l_Lean_findOLean___closed__7;
x_104 = lean_string_append(x_103, x_94);
lean_dec(x_94);
x_105 = l_Lean_findOLean___closed__8;
x_106 = lean_string_append(x_104, x_105);
x_107 = 1;
x_108 = l_Lean_Name_toString(x_1, x_107);
x_109 = lean_string_append(x_106, x_108);
lean_dec(x_108);
x_110 = l_Lean_findOLean___closed__9;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_102;
 lean_ctor_set_tag(x_113, 1);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_101);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_1);
x_114 = lean_ctor_get(x_95, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_115 = x_95;
} else {
 lean_dec_ref(x_95);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_94);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_94);
lean_dec(x_1);
x_117 = lean_ctor_get(x_95, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_95, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_119 = x_95;
} else {
 lean_dec_ref(x_95);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_12);
if (x_121 == 0)
{
return x_12;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_12, 0);
x_123 = lean_ctor_get(x_12, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_12);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_findOLean(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_dec(x_2);
x_5 = l_Lean_Name_str___override(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_string_length(x_1);
x_6 = l_String_drop(x_2, x_5);
x_7 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_8 = l_System_FilePath_withExtension(x_6, x_7);
x_9 = l_System_FilePath_components(x_8);
x_10 = lean_box(0);
x_11 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_10, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("input file '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' must be contained in root directory (", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_5 = l_System_FilePath_normalize(x_1);
x_6 = l_String_isPrefixOf(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_moduleNameOfFileName___lambda__2___closed__1;
x_8 = lean_string_append(x_7, x_1);
lean_dec(x_1);
x_9 = l_Lean_moduleNameOfFileName___lambda__2___closed__2;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_string_append(x_10, x_2);
x_12 = l_Lean_moduleNameOfFileName___lambda__2___closed__3;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_moduleNameOfFileName___lambda__1(x_2, x_1, x_16, x_4);
return x_17;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__3___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_realPathNormalized(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_moduleNameOfFileName___lambda__3___closed__1;
lean_inc(x_5);
x_8 = l_String_endsWith(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_string_append(x_5, x_7);
x_10 = lean_box(0);
x_11 = l_Lean_moduleNameOfFileName___lambda__2(x_1, x_9, x_10, x_6);
lean_dec(x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_moduleNameOfFileName___lambda__2(x_1, x_5, x_12, x_6);
lean_dec(x_5);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lean_module_name_of_file(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_realpath(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_io_current_dir(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_moduleNameOfFileName___lambda__3(x_5, x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_moduleNameOfFileName___lambda__3(x_15, x_17, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
return x_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleNameOfFileName___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleNameOfFileName___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
lean_inc(x_1);
x_11 = lean_module_name_of_file(x_1, x_10, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_free_object(x_3);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_9;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_4 = x_23;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
lean_inc(x_1);
x_28 = lean_module_name_of_file(x_1, x_27, x_5);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_dec(x_28);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_26;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_4 = x_37;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_searchModuleNameOfFileName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_Lean_searchModuleNameOfFileName___closed__1;
x_6 = l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1(x_1, x_5, x_2, x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_searchModuleNameOfFileName___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_findSysroot___lambda__1___closed__1() {
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
static lean_object* _init_l_Lean_findSysroot___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_findSysroot___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--print-prefix", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_findSysroot___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_findSysroot___lambda__1___closed__2;
x_2 = l_Lean_findSysroot___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = l_Lean_findSysroot___lambda__1___closed__1;
x_6 = l_Lean_findSysroot___lambda__1___closed__4;
x_7 = l_Lean_SearchPath_findAllWithExt___closed__1;
x_8 = 0;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_8);
x_10 = l_IO_Process_run(x_9, x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_String_trim(x_12);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_String_trim(x_14);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l_Lean_findSysroot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LEAN_SYSROOT", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_findSysroot___closed__1;
x_4 = lean_io_getenv(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = l_Lean_findSysroot___lambda__1(x_1, x_7, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findSysroot___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__1);
l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__2);
l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_forEachModuleInDir___spec__2___rarg___lambda__5___closed__3);
l_Lean_modToFilePath_go___closed__1 = _init_l_Lean_modToFilePath_go___closed__1();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__1);
l_Lean_modToFilePath_go___closed__2 = _init_l_Lean_modToFilePath_go___closed__2();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__2);
l_Lean_modToFilePath_go___closed__3 = _init_l_Lean_modToFilePath_go___closed__3();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__3);
l_Lean_modToFilePath_go___closed__4 = _init_l_Lean_modToFilePath_go___closed__4();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__4);
l_panic___at_Lean_moduleExists_go___spec__2___closed__1 = _init_l_panic___at_Lean_moduleExists_go___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_moduleExists_go___spec__2___closed__1);
l_Lean_moduleExists_go___closed__1 = _init_l_Lean_moduleExists_go___closed__1();
lean_mark_persistent(l_Lean_moduleExists_go___closed__1);
l_Lean_moduleExists_go___closed__2 = _init_l_Lean_moduleExists_go___closed__2();
lean_mark_persistent(l_Lean_moduleExists_go___closed__2);
l_Lean_moduleExists_go___closed__3 = _init_l_Lean_moduleExists_go___closed__3();
lean_mark_persistent(l_Lean_moduleExists_go___closed__3);
l_Lean_SearchPath_findModuleWithExt___closed__1 = _init_l_Lean_SearchPath_findModuleWithExt___closed__1();
lean_mark_persistent(l_Lean_SearchPath_findModuleWithExt___closed__1);
l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__2___closed__1);
l_Lean_SearchPath_findAllWithExt___closed__1 = _init_l_Lean_SearchPath_findAllWithExt___closed__1();
lean_mark_persistent(l_Lean_SearchPath_findAllWithExt___closed__1);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_Path___hyg_1117_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
}l_Lean_getBuildDir___closed__1 = _init_l_Lean_getBuildDir___closed__1();
lean_mark_persistent(l_Lean_getBuildDir___closed__1);
l_Lean_getBuildDir___closed__2 = _init_l_Lean_getBuildDir___closed__2();
lean_mark_persistent(l_Lean_getBuildDir___closed__2);
l_Lean_getBuildDir___closed__3 = _init_l_Lean_getBuildDir___closed__3();
lean_mark_persistent(l_Lean_getBuildDir___closed__3);
l_Lean_getBuildDir___closed__4 = _init_l_Lean_getBuildDir___closed__4();
lean_mark_persistent(l_Lean_getBuildDir___closed__4);
l_Lean_getLibDir___lambda__1___closed__1 = _init_l_Lean_getLibDir___lambda__1___closed__1();
lean_mark_persistent(l_Lean_getLibDir___lambda__1___closed__1);
l_Lean_getLibDir___closed__1 = _init_l_Lean_getLibDir___closed__1();
lean_mark_persistent(l_Lean_getLibDir___closed__1);
l_Lean_getLibDir___closed__2 = _init_l_Lean_getLibDir___closed__2();
l_Lean_getLibDir___closed__3 = _init_l_Lean_getLibDir___closed__3();
lean_mark_persistent(l_Lean_getLibDir___closed__3);
l_Lean_getLibDir___closed__4 = _init_l_Lean_getLibDir___closed__4();
lean_mark_persistent(l_Lean_getLibDir___closed__4);
l_Lean_addSearchPathFromEnv___closed__1 = _init_l_Lean_addSearchPathFromEnv___closed__1();
lean_mark_persistent(l_Lean_addSearchPathFromEnv___closed__1);
l_Lean_initSearchPath___closed__1 = _init_l_Lean_initSearchPath___closed__1();
lean_mark_persistent(l_Lean_initSearchPath___closed__1);
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
l_Lean_findOLean___closed__6 = _init_l_Lean_findOLean___closed__6();
lean_mark_persistent(l_Lean_findOLean___closed__6);
l_Lean_findOLean___closed__7 = _init_l_Lean_findOLean___closed__7();
lean_mark_persistent(l_Lean_findOLean___closed__7);
l_Lean_findOLean___closed__8 = _init_l_Lean_findOLean___closed__8();
lean_mark_persistent(l_Lean_findOLean___closed__8);
l_Lean_findOLean___closed__9 = _init_l_Lean_findOLean___closed__9();
lean_mark_persistent(l_Lean_findOLean___closed__9);
l_Lean_moduleNameOfFileName___lambda__2___closed__1 = _init_l_Lean_moduleNameOfFileName___lambda__2___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__2___closed__1);
l_Lean_moduleNameOfFileName___lambda__2___closed__2 = _init_l_Lean_moduleNameOfFileName___lambda__2___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__2___closed__2);
l_Lean_moduleNameOfFileName___lambda__2___closed__3 = _init_l_Lean_moduleNameOfFileName___lambda__2___closed__3();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__2___closed__3);
l_Lean_moduleNameOfFileName___lambda__3___closed__1 = _init_l_Lean_moduleNameOfFileName___lambda__3___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__3___closed__1);
l_Lean_searchModuleNameOfFileName___closed__1 = _init_l_Lean_searchModuleNameOfFileName___closed__1();
lean_mark_persistent(l_Lean_searchModuleNameOfFileName___closed__1);
l_Lean_findSysroot___lambda__1___closed__1 = _init_l_Lean_findSysroot___lambda__1___closed__1();
lean_mark_persistent(l_Lean_findSysroot___lambda__1___closed__1);
l_Lean_findSysroot___lambda__1___closed__2 = _init_l_Lean_findSysroot___lambda__1___closed__2();
lean_mark_persistent(l_Lean_findSysroot___lambda__1___closed__2);
l_Lean_findSysroot___lambda__1___closed__3 = _init_l_Lean_findSysroot___lambda__1___closed__3();
lean_mark_persistent(l_Lean_findSysroot___lambda__1___closed__3);
l_Lean_findSysroot___lambda__1___closed__4 = _init_l_Lean_findSysroot___lambda__1___closed__4();
lean_mark_persistent(l_Lean_findSysroot___lambda__1___closed__4);
l_Lean_findSysroot___closed__1 = _init_l_Lean_findSysroot___closed__1();
lean_mark_persistent(l_Lean_findSysroot___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
