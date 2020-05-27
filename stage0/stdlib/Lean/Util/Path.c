// Lean compiler output
// Module: Lean.Util.Path
// Imports: Init.System.IO Init.System.FilePath Init.Data.Array Init.Data.List.Control Init.Data.HashMap Init.Data.Nat.Control Lean.Data.Name
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_IO_isDir___at_Lean_findOLean___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* l___private_Lean_Util_Path_1__pathSep;
lean_object* l_Lean_searchPathRef;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
lean_object* l_Lean_mkSearchPathRef(lean_object*);
lean_object* l_Lean_parseSearchPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__3;
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__2;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__1;
lean_object* l_Lean_modPathToFilePath___main(lean_object*);
lean_object* l_IO_currentDir___at_Lean_moduleNameOfFileName___spec__1(lean_object*);
lean_object* lean_io_current_dir(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__1;
lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__1;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_System_FilePath_normalizePath(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_findOLean___closed__2;
lean_object* l_Lean_modPathToFilePath___boxed(lean_object*);
lean_object* l_Lean_modPathToFilePath___main___boxed(lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__4;
extern uint32_t l_System_FilePath_pathSeparator;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2(lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(lean_object*, lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__3;
lean_object* l_List_findM_x3f___main___at_Lean_findOLean___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_isDir___at_Lean_findOLean___spec__1(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_findOLean___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__2;
extern lean_object* l_System_mkFilePath___closed__1;
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseSearchPath(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object*);
lean_object* l_Lean_Name_getRoot___main(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_modPathToFilePath(lean_object*);
lean_object* l_List_findM_x3f___main___at_Lean_findOLean___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__3;
extern lean_object* l_String_Inhabited;
lean_object* l_IO_realPath___at_Lean_realPathNormalized___spec__1(lean_object*, lean_object*);
lean_object* _init_l___private_Lean_Util_Path_1__pathSep() {
_start:
{
lean_object* x_1; 
x_1 = l_System_mkFilePath___closed__1;
return x_1;
}
}
lean_object* l_IO_realPath___at_Lean_realPathNormalized___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_realPathNormalized(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_System_FilePath_normalizePath(x_5);
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
x_9 = l_System_FilePath_normalizePath(x_7);
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
lean_object* l_Lean_mkSearchPathRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_parseSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_String_split___at_System_FilePath_splitSearchPath___spec__2(x_1);
x_5 = l_List_append___rarg(x_4, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_parseSearchPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_parseSearchPath(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_dir(x_1);
return x_2;
}
}
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_app_dir(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_System_FilePath_dirName(x_3);
x_6 = lean_io_realpath(x_5, x_4);
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
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("..");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean");
return x_1;
}
}
lean_object* l_Lean_getBuiltinSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Util_Path_1__pathSep;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lean_getBuiltinSearchPath___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_5);
x_10 = l_Lean_getBuiltinSearchPath___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_5);
x_13 = l_Lean_getBuiltinSearchPath___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = l___private_Lean_Util_Path_1__pathSep;
x_20 = lean_string_append(x_17, x_19);
x_21 = l_Lean_getBuiltinSearchPath___closed__1;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_19);
x_24 = l_Lean_getBuiltinSearchPath___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_19);
x_27 = l_Lean_getBuiltinSearchPath___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_addSearchPathFromEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_PATH");
return x_1;
}
}
lean_object* l_Lean_addSearchPathFromEnv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_addSearchPathFromEnv___closed__1;
x_4 = lean_io_getenv(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = l_Lean_parseSearchPath(x_11, x_1, x_10);
lean_dec(x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_init_search_path(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_Lean_getBuiltinSearchPath(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_addSearchPathFromEnv(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_searchPathRef;
x_10 = lean_io_ref_set(x_9, x_7, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = l_Lean_parseSearchPath(x_19, x_20, x_2);
lean_dec(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_searchPathRef;
x_25 = lean_io_ref_set(x_24, x_22, x_23);
return x_25;
}
}
}
lean_object* _init_l_Lean_modPathToFilePath___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Util.Path");
return x_1;
}
}
lean_object* _init_l_Lean_modPathToFilePath___main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed import");
return x_1;
}
}
lean_object* _init_l_Lean_modPathToFilePath___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_modPathToFilePath___main___closed__1;
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(33u);
x_4 = l_Lean_modPathToFilePath___main___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_modPathToFilePath___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_modPathToFilePath___main(x_3);
x_6 = l___private_Lean_Util_Path_1__pathSep;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_7, x_4);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_String_Inhabited;
x_10 = l_Lean_modPathToFilePath___main___closed__3;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_modPathToFilePath___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modPathToFilePath___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_modPathToFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modPathToFilePath___main(x_1);
return x_2;
}
}
lean_object* l_Lean_modPathToFilePath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modPathToFilePath(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_IO_isDir___at_Lean_findOLean___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
return x_3;
}
}
lean_object* l_List_findM_x3f___main___at_Lean_findOLean___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l___private_Lean_Util_Path_1__pathSep;
lean_inc(x_6);
x_9 = lean_string_append(x_6, x_8);
x_10 = lean_string_append(x_9, x_1);
x_11 = lean_io_is_dir(x_10, x_3);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_2 = x_7;
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* _init_l_Lean_findOLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown package '");
return x_1;
}
}
lean_object* _init_l_Lean_findOLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".olean");
return x_1;
}
}
lean_object* l_Lean_findOLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_searchPathRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Name_getRoot___main(x_1);
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
x_10 = l_List_findM_x3f___main___at_Lean_findOLean___spec__2(x_9, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Lean_findOLean___closed__1;
x_15 = lean_string_append(x_14, x_9);
lean_dec(x_9);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_findOLean___closed__1;
x_21 = lean_string_append(x_20, x_9);
lean_dec(x_9);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_9);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = l_Lean_modPathToFilePath___main(x_1);
x_30 = lean_string_append(x_28, x_29);
lean_dec(x_29);
x_31 = l_Lean_findOLean___closed__2;
x_32 = lean_string_append(x_30, x_31);
lean_ctor_set(x_10, 0, x_32);
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_dec(x_10);
x_34 = lean_ctor_get(x_11, 0);
lean_inc(x_34);
lean_dec(x_11);
x_35 = l_Lean_modPathToFilePath___main(x_1);
x_36 = lean_string_append(x_34, x_35);
lean_dec(x_35);
x_37 = l_Lean_findOLean___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_9);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_4);
if (x_44 == 0)
{
return x_4;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_IO_isDir___at_Lean_findOLean___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir___at_Lean_findOLean___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_findM_x3f___main___at_Lean_findOLean___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_findM_x3f___main___at_Lean_findOLean___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_findOLean___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_findOLean(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_currentDir___at_Lean_moduleNameOfFileName___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir(x_1);
return x_2;
}
}
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_name_mk_string(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to convert file name '");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' to module name, extension is missing");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input file '");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' must be contained in current directory (");
return x_1;
}
}
lean_object* lean_module_name_of_file(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_realPathNormalized(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_io_current_dir(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_realPathNormalized(x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; uint8_t x_20; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = l_String_isPrefixOf(x_10, x_4);
x_14 = lean_string_length(x_10);
x_15 = l_String_drop(x_4, x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_get(x_15, x_16);
x_18 = l_System_FilePath_pathSeparator;
x_19 = x_17 == x_18;
if (x_13 == 0)
{
uint8_t x_80; 
x_80 = 1;
x_20 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = 0;
x_20 = x_81;
goto block_79;
}
block_79:
{
uint8_t x_21; 
if (x_20 == 0)
{
uint8_t x_77; 
x_77 = 0;
x_21 = x_77;
goto block_76;
}
else
{
uint8_t x_78; 
x_78 = 1;
x_21 = x_78;
goto block_76;
}
block_76:
{
uint8_t x_22; 
if (x_19 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_22 = x_74;
goto block_73;
}
else
{
uint8_t x_75; 
x_75 = 1;
x_22 = x_75;
goto block_73;
}
block_73:
{
if (x_22 == 0)
{
if (x_21 == 0)
{
uint32_t x_23; lean_object* x_24; 
lean_dec(x_10);
x_23 = 46;
x_24 = l_String_revPosOf(x_15, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_25 = l_Lean_moduleNameOfFileName___closed__1;
x_26 = lean_string_append(x_25, x_4);
lean_dec(x_4);
x_27 = l_Lean_moduleNameOfFileName___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
if (lean_is_scalar(x_12)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_12;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_11);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_string_utf8_extract(x_15, x_16, x_31);
lean_dec(x_31);
lean_dec(x_15);
x_33 = l___private_Lean_Util_Path_1__pathSep;
x_34 = l_String_splitOn(x_32, x_33);
x_35 = lean_box(0);
x_36 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__2(x_35, x_34);
if (lean_is_scalar(x_12)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_12;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_15);
x_38 = l_Lean_moduleNameOfFileName___closed__3;
x_39 = lean_string_append(x_38, x_4);
lean_dec(x_4);
x_40 = l_Lean_moduleNameOfFileName___closed__4;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_10);
lean_dec(x_10);
x_43 = l_Option_HasRepr___rarg___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_12)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_12;
 lean_ctor_set_tag(x_46, 1);
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_11);
return x_46;
}
}
else
{
if (x_21 == 0)
{
lean_object* x_47; lean_object* x_48; uint32_t x_49; lean_object* x_50; 
lean_dec(x_10);
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_String_drop(x_15, x_47);
lean_dec(x_15);
x_49 = 46;
x_50 = l_String_revPosOf(x_48, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_51 = l_Lean_moduleNameOfFileName___closed__1;
x_52 = lean_string_append(x_51, x_4);
lean_dec(x_4);
x_53 = l_Lean_moduleNameOfFileName___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_55, 0, x_54);
if (lean_is_scalar(x_12)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_12;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_11);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_4);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
lean_dec(x_50);
x_58 = lean_string_utf8_extract(x_48, x_16, x_57);
lean_dec(x_57);
lean_dec(x_48);
x_59 = l___private_Lean_Util_Path_1__pathSep;
x_60 = l_String_splitOn(x_58, x_59);
x_61 = lean_box(0);
x_62 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__2(x_61, x_60);
if (lean_is_scalar(x_12)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_12;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_11);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_15);
x_64 = l_Lean_moduleNameOfFileName___closed__3;
x_65 = lean_string_append(x_64, x_4);
lean_dec(x_4);
x_66 = l_Lean_moduleNameOfFileName___closed__4;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_10);
lean_dec(x_10);
x_69 = l_Option_HasRepr___rarg___closed__3;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_12)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_12;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
return x_72;
}
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_9);
if (x_82 == 0)
{
return x_9;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_9, 0);
x_84 = lean_ctor_get(x_9, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_9);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
return x_6;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_6, 0);
x_88 = lean_ctor_get(x_6, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_6);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_3);
if (x_90 == 0)
{
return x_3;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_3, 0);
x_92 = lean_ctor_get(x_3, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_3);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_System_FilePath(lean_object*);
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Data_List_Control(lean_object*);
lean_object* initialize_Init_Data_HashMap(lean_object*);
lean_object* initialize_Init_Data_Nat_Control(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Path(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_Path_1__pathSep = _init_l___private_Lean_Util_Path_1__pathSep();
lean_mark_persistent(l___private_Lean_Util_Path_1__pathSep);
res = l_Lean_mkSearchPathRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__1);
l_Lean_getBuiltinSearchPath___closed__2 = _init_l_Lean_getBuiltinSearchPath___closed__2();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__2);
l_Lean_getBuiltinSearchPath___closed__3 = _init_l_Lean_getBuiltinSearchPath___closed__3();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__3);
l_Lean_addSearchPathFromEnv___closed__1 = _init_l_Lean_addSearchPathFromEnv___closed__1();
lean_mark_persistent(l_Lean_addSearchPathFromEnv___closed__1);
l_Lean_modPathToFilePath___main___closed__1 = _init_l_Lean_modPathToFilePath___main___closed__1();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__1);
l_Lean_modPathToFilePath___main___closed__2 = _init_l_Lean_modPathToFilePath___main___closed__2();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__2);
l_Lean_modPathToFilePath___main___closed__3 = _init_l_Lean_modPathToFilePath___main___closed__3();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__3);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean_mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findOLean___closed__2 = _init_l_Lean_findOLean___closed__2();
lean_mark_persistent(l_Lean_findOLean___closed__2);
l_Lean_moduleNameOfFileName___closed__1 = _init_l_Lean_moduleNameOfFileName___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__1);
l_Lean_moduleNameOfFileName___closed__2 = _init_l_Lean_moduleNameOfFileName___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__2);
l_Lean_moduleNameOfFileName___closed__3 = _init_l_Lean_moduleNameOfFileName___closed__3();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__3);
l_Lean_moduleNameOfFileName___closed__4 = _init_l_Lean_moduleNameOfFileName___closed__4();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
