// Lean compiler output
// Module: Lean.Util.Path
// Imports: Init Lean.Data.Name
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
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_String_endsWith(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__3___closed__1;
LEAN_EXPORT lean_object* lean_init_search_path(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_getLibDir___closed__1;
lean_object* l_System_FilePath_walkDir(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_modToFilePath_go___spec__1(lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean_maybeThisOne___closed__1;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__3;
lean_object* l_System_SearchPath_parse(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_modToFilePath_go___closed__3;
static lean_object* l_Lean_findSysroot___lambda__1___closed__2;
static lean_object* l_Lean_SearchPath_findAllWithExt___closed__1;
lean_object* l_String_trim(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getLibDir___closed__4;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__4;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_findSysroot___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean___closed__1;
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initSearchPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_findOLean___closed__3;
LEAN_EXPORT lean_object* l_Lean_findSysroot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_findOLean_maybeThisOne___closed__2;
static lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1;
lean_object* l_System_FilePath_isDir(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___lambda__1___closed__4;
static lean_object* l_Lean_modToFilePath_go___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_IO_appDir(lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__2;
static lean_object* l_Lean_modToFilePath_go___closed__2;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_initSearchPath___closed__1;
static lean_object* l_Lean_getLibDir___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__1;
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__3;
LEAN_EXPORT lean_object* l_Lean_findOLean___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getBuildDir___closed__4;
static lean_object* l_Lean_findSysroot___lambda__1___closed__1;
LEAN_EXPORT lean_object* lean_get_prefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_internal_is_stage0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean_maybeThisOne___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Lean_getBuildDir___closed__1;
LEAN_EXPORT lean_object* l_Lean_findOLean_maybeThisOne(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchPathRef;
LEAN_EXPORT lean_object* l_Lean_SearchPath_findModuleWithExt___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findSysroot___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_instInhabitedFilePath;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_Lean_searchModuleNameOfFileName___closed__1;
static lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinSearchPath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath_go(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_moduleNameOfFileName___lambda__1___closed__1;
static lean_object* l_Lean_findOLean___closed__2;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_current_dir(lean_object*);
static uint8_t l_Lean_getLibDir___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_608_(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_getLibDir___lambda__1___closed__1;
static lean_object* l_Lean_getLibDir___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_get_libdir(lean_object*, lean_object*);
static lean_object* l_Lean_SearchPath_findModuleWithExt___closed__1;
lean_object* l_IO_Process_run(lean_object*, lean_object*);
static lean_object* l_Lean_findSysroot___lambda__1___closed__3;
lean_object* l_String_drop(lean_object*, lean_object*);
static lean_object* l_Lean_modToFilePath_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_SearchPath_findAllWithExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
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
x_1 = lean_mk_string_from_bytes("Lean.Util.Path", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.modToFilePath.go", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed import", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_modToFilePath_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_modToFilePath_go___closed__1;
x_2 = l_Lean_modToFilePath_go___closed__2;
x_3 = lean_unsigned_to_nat(25u);
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
lean_dec(x_1);
x_7 = l_Lean_modToFilePath_go___closed__4;
x_8 = l_panic___at_Lean_modToFilePath_go___spec__1(x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_modToFilePath_go(x_1, x_2);
x_5 = l_System_FilePath_withExtension(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_modToFilePath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_modToFilePath(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_7);
x_9 = l_System_FilePath_join(x_7, x_2);
x_10 = l_System_FilePath_isDir(x_9, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_System_FilePath_withExtension(x_9, x_1);
x_15 = l_System_FilePath_pathExists(x_14, x_13);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_7);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_3 = x_8;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_7);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_7);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SearchPath_findWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = 1;
x_7 = l_Lean_Name_toString(x_5, x_6);
x_8 = l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1(x_2, x_7, x_1, x_4);
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
}
LEAN_EXPORT lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_SearchPath_findModuleWithExt___closed__1;
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, x_9, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = l_System_FilePath_pathExists(x_12, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_free_object(x_6);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_8, x_17, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_System_FilePath_pathExists(x_23, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_apply_2(x_8, x_28, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_23);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
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
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
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
x_10 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1(x_8, x_9);
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_15 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1;
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
lean_inc(x_2);
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
lean_inc(x_2);
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
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2(x_1, x_17, x_27, x_28, x_2);
lean_dec(x_17);
x_30 = l_Array_append___rarg(x_4, x_29);
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
x_5 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3(x_2, x_4, x_1, x_4, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_1119____at_Lean_SearchPath_findAllWithExt___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_SearchPath_findAllWithExt___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_608_(lean_object* x_1) {
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
x_1 = lean_mk_string_from_bytes("Init.Data.Option.BasicAux", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Option.get!", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_getBuildDir___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value is none", 13);
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
lean_dec(x_4);
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
lean_dec(x_9);
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
x_1 = lean_mk_string_from_bytes("lib", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_getLibDir___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_getLibDir___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_getLibDir___lambda__1___closed__1;
x_5 = l_System_FilePath_join(x_1, x_4);
x_6 = l_Lean_getLibDir___lambda__1___closed__2;
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
x_1 = lean_mk_string_from_bytes("..", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_getLibDir___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stage1", 6);
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
x_1 = lean_mk_string_from_bytes("LEAN_PATH", 9);
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
LEAN_EXPORT lean_object* l_Lean_findOLean_maybeThisOne___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = l_System_FilePath_parent(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_findOLean_maybeThisOne(x_2, x_8, x_4);
return x_9;
}
}
}
static lean_object* _init_l_Lean_findOLean_maybeThisOne___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nYou might need to open '", 25);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean_maybeThisOne___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' as a workspace in your editor", 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean_maybeThisOne(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
lean_inc(x_2);
x_4 = l_System_FilePath_join(x_2, x_1);
x_5 = l_System_FilePath_isDir(x_4, x_3);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = l_Lean_findOLean_maybeThisOne___lambda__1(x_2, x_1, x_9, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
x_13 = l_Lean_findOLean_maybeThisOne___closed__1;
x_14 = lean_string_append(x_13, x_2);
lean_dec(x_2);
x_15 = l_Lean_findOLean_maybeThisOne___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Lean_findOLean_maybeThisOne___closed__1;
x_20 = lean_string_append(x_19, x_2);
lean_dec(x_2);
x_21 = l_Lean_findOLean_maybeThisOne___closed__2;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_findOLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("olean", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown package '", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_findOLean___lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_initSearchPath___closed__1;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_findOLean___closed__1;
lean_inc(x_1);
x_8 = l_Lean_SearchPath_findWithExt(x_5, x_7, x_1, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
x_12 = 1;
x_13 = l_Lean_Name_toString(x_11, x_12);
x_14 = l_Lean_findOLean___closed__2;
x_15 = lean_string_append(x_14, x_13);
x_16 = l_Lean_findOLean___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_io_current_dir(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_findOLean_maybeThisOne(x_13, x_19, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_findOLean___closed__4;
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = lean_apply_3(x_24, x_17, x_25, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_string_append(x_17, x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = lean_apply_3(x_24, x_28, x_29, x_23);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_9, 0);
lean_inc(x_37);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_37);
return x_8;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_dec(x_8);
x_39 = lean_ctor_get(x_9, 0);
lean_inc(x_39);
lean_dec(x_9);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findOLean___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findOLean___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
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
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_string_length(x_1);
x_6 = l_String_drop(x_2, x_5);
x_7 = l_Lean_moduleNameOfFileName___lambda__1___closed__1;
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
x_1 = lean_mk_string_from_bytes("input file '", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' must be contained in root directory (", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_3);
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
lean_dec(x_2);
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
lean_dec(x_2);
return x_17;
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__3___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_Lean_moduleNameOfFileName___lambda__1___closed__1;
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
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_moduleNameOfFileName___lambda__2(x_1, x_5, x_12, x_6);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
lean_inc(x_1);
x_10 = lean_module_name_of_file(x_1, x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
lean_inc(x_2);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_2;
lean_object* _tmp_4 = x_24;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
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
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_forIn_loop___at_Lean_searchModuleNameOfFileName___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_searchModuleNameOfFileName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_searchModuleNameOfFileName(x_1, x_2, x_3);
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
x_1 = lean_mk_string_from_bytes("--print-prefix", 14);
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
x_1 = lean_mk_string_from_bytes("LEAN_SYSROOT", 12);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Path(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_modToFilePath_go___closed__1 = _init_l_Lean_modToFilePath_go___closed__1();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__1);
l_Lean_modToFilePath_go___closed__2 = _init_l_Lean_modToFilePath_go___closed__2();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__2);
l_Lean_modToFilePath_go___closed__3 = _init_l_Lean_modToFilePath_go___closed__3();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__3);
l_Lean_modToFilePath_go___closed__4 = _init_l_Lean_modToFilePath_go___closed__4();
lean_mark_persistent(l_Lean_modToFilePath_go___closed__4);
l_Lean_SearchPath_findModuleWithExt___closed__1 = _init_l_Lean_SearchPath_findModuleWithExt___closed__1();
lean_mark_persistent(l_Lean_SearchPath_findModuleWithExt___closed__1);
l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1 = _init_l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_SearchPath_findAllWithExt___spec__3___closed__1);
l_Lean_SearchPath_findAllWithExt___closed__1 = _init_l_Lean_SearchPath_findAllWithExt___closed__1();
lean_mark_persistent(l_Lean_SearchPath_findAllWithExt___closed__1);
if (builtin) {res = l_Lean_initFn____x40_Lean_Util_Path___hyg_608_(lean_io_mk_world());
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
l_Lean_getLibDir___lambda__1___closed__2 = _init_l_Lean_getLibDir___lambda__1___closed__2();
lean_mark_persistent(l_Lean_getLibDir___lambda__1___closed__2);
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
l_Lean_findOLean_maybeThisOne___closed__1 = _init_l_Lean_findOLean_maybeThisOne___closed__1();
lean_mark_persistent(l_Lean_findOLean_maybeThisOne___closed__1);
l_Lean_findOLean_maybeThisOne___closed__2 = _init_l_Lean_findOLean_maybeThisOne___closed__2();
lean_mark_persistent(l_Lean_findOLean_maybeThisOne___closed__2);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean_mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findOLean___closed__2 = _init_l_Lean_findOLean___closed__2();
lean_mark_persistent(l_Lean_findOLean___closed__2);
l_Lean_findOLean___closed__3 = _init_l_Lean_findOLean___closed__3();
lean_mark_persistent(l_Lean_findOLean___closed__3);
l_Lean_findOLean___closed__4 = _init_l_Lean_findOLean___closed__4();
lean_mark_persistent(l_Lean_findOLean___closed__4);
l_Lean_moduleNameOfFileName___lambda__1___closed__1 = _init_l_Lean_moduleNameOfFileName___lambda__1___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__1___closed__1);
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
