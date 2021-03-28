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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__6;
lean_object* l_Lean_findOLean___closed__3;
extern lean_object* l_String_instInhabitedString;
extern lean_object* l_Char_quote___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* l_Lean_modPathToFilePath_match__1(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_searchPathRef;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
lean_object* l_Lean_parseSearchPath___boxed(lean_object*, lean_object*);
lean_object* l_IO_isDir___at_Lean_SearchPath_findWithExt___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_Path___hyg_199____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__1;
lean_object* l_Lean_moduleNameOfFileName_match__1(lean_object*);
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_formatStxAux___closed__3;
lean_object* l_Lean_findOLean_maybeThisOne___closed__2;
lean_object* l_Lean_findOLean_maybeThisOne___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_current_dir(lean_object*);
uint8_t l_Lean_getBuiltinSearchPath___closed__1;
lean_object* l_Lean_moduleNameOfFileName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___lambda__1___closed__1;
lean_object* l_IO_currentDir___at_Lean_findOLean___spec__1(lean_object*);
lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* l_IO_fileExists___at_Lean_SearchPath_findWithExt___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___closed__4;
lean_object* l_Lean_moduleNameOfFileName___lambda__1___closed__2;
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___closed__1;
lean_object* l___private_Lean_Util_Path_0__Lean_isStage0___boxed(lean_object*);
lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalizePath(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__5;
lean_object* l_Lean_findOLean___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___closed__2;
lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_199_(lean_object*);
lean_object* l_Lean_findOLean___closed__2;
lean_object* l_Lean_modPathToFilePath___boxed(lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* l_Lean_modPathToFilePath___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_findOLean___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initSearchPath_match__1(lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv_match__1(lean_object*);
lean_object* l_Lean_findOLean___closed__1;
lean_object* lean_io_file_exists(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_Lean_findOLean___boxed(lean_object*, lean_object*);
lean_object* l_IO_isDir___at_Lean_SearchPath_findWithExt___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_findOLean_maybeThisOne_match__1(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_IO_appDir___rarg___lambda__1___closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
lean_object* l_Lean_findOLean_maybeThisOne_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__2;
lean_object* l_Lean_moduleNameOfFileName_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findOLean_maybeThisOne___closed__1;
lean_object* l_IO_fileExists___at_Lean_SearchPath_findWithExt___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__4;
extern lean_object* l_System_mkFilePath___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__7;
lean_object* l_Lean_initSearchPath_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseSearchPath(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Path_0__Lean_isStage0(lean_object*);
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object*);
lean_object* l_Lean_moduleNameOfFileName___lambda__2___closed__2;
lean_object* l_Lean_moduleNameOfFileName_match__2(lean_object*);
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* lean_string_length(lean_object*);
lean_object* l_System_FilePath_parent(lean_object*);
lean_object* l_Lean_modPathToFilePath(lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_findOLean_maybeThisOne(lean_object*, lean_object*, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__3;
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__1(lean_object*);
lean_object* l___private_Lean_Util_Path_0__Lean_pathSep;
lean_object* l_IO_realPath___at_Lean_realPathNormalized___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_findOLean_maybeThisOne___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Util_Path_0__Lean_pathSep() {
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
lean_object* l_Lean_modPathToFilePath_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_10 = lean_box_usize(x_9);
x_11 = lean_apply_3(x_2, x_7, x_8, x_10);
return x_11;
}
default: 
{
lean_object* x_12; lean_object* x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_15 = lean_box_usize(x_14);
x_16 = lean_apply_3(x_4, x_12, x_13, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_modPathToFilePath_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_modPathToFilePath_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_modPathToFilePath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Util.Path");
return x_1;
}
}
static lean_object* _init_l_Lean_modPathToFilePath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.modPathToFilePath");
return x_1;
}
}
static lean_object* _init_l_Lean_modPathToFilePath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed import");
return x_1;
}
}
static lean_object* _init_l_Lean_modPathToFilePath___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_modPathToFilePath___closed__1;
x_2 = l_Lean_modPathToFilePath___closed__2;
x_3 = lean_unsigned_to_nat(24u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_modPathToFilePath___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_modPathToFilePath(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_modPathToFilePath(x_3);
x_6 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_string_append(x_7, x_4);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_String_instInhabitedString;
x_10 = l_Lean_modPathToFilePath___closed__4;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
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
lean_object* l_IO_isDir___at_Lean_SearchPath_findWithExt___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
return x_3;
}
}
lean_object* l_IO_fileExists___at_Lean_SearchPath_findWithExt___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
return x_3;
}
}
lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_9, x_7);
x_11 = lean_string_append(x_10, x_9);
x_12 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_string_append(x_13, x_9);
x_15 = lean_string_append(x_14, x_2);
x_16 = lean_string_append(x_15, x_9);
x_17 = lean_io_is_dir(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_string_append(x_16, x_1);
x_22 = lean_string_append(x_21, x_9);
x_23 = lean_io_file_exists(x_22, x_20);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_3 = x_8;
x_4 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
lean_inc(x_7);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_7);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_16);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_17, 0);
lean_dec(x_39);
lean_inc(x_7);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_17, 0, x_40);
return x_17;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
lean_inc(x_7);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_7);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_16);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Lean_SearchPath_findWithExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Name_getRoot(x_3);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep(x_6, x_5);
x_8 = l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3(x_2, x_7, x_1, x_4);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = l_Lean_modPathToFilePath(x_3);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_string_append(x_21, x_2);
lean_ctor_set(x_9, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = l_Lean_modPathToFilePath(x_3);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_25, x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_8, 0, x_27);
return x_8;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_8, 1);
lean_inc(x_28);
lean_dec(x_8);
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_30 = x_9;
} else {
 lean_dec_ref(x_9);
 x_30 = lean_box(0);
}
x_31 = l_Lean_modPathToFilePath(x_3);
x_32 = lean_string_append(x_29, x_31);
lean_dec(x_31);
x_33 = lean_string_append(x_32, x_2);
if (lean_is_scalar(x_30)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_30;
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_8);
if (x_36 == 0)
{
return x_8;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_8, 0);
x_38 = lean_ctor_get(x_8, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_IO_isDir___at_Lean_SearchPath_findWithExt___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir___at_Lean_SearchPath_findWithExt___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_fileExists___at_Lean_SearchPath_findWithExt___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_fileExists___at_Lean_SearchPath_findWithExt___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_findM_x3f___at_Lean_SearchPath_findWithExt___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_SearchPath_findWithExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SearchPath_findWithExt(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_Path___hyg_199____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
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
lean_object* l_Lean_initFn____x40_Lean_Util_Path___hyg_199_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_Util_Path___hyg_199____spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_parseSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_split___at_System_FilePath_splitSearchPath___spec__1(x_1);
x_4 = l_List_append___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_parseSearchPath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_parseSearchPath(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Util_Path_0__Lean_isStage0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = LEAN_IS_STAGE0;
x_3 = lean_box(x_2);
return x_3;
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
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_6 = l_System_FilePath_parent(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_IO_appDir___rarg___lambda__1___closed__1;
x_8 = lean_string_append(x_7, x_4);
lean_dec(x_4);
x_9 = l_Char_quote___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_4);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_io_realpath(x_12, x_5);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_14);
x_16 = l_System_FilePath_parent(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_IO_appDir___rarg___lambda__1___closed__1;
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Char_quote___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_io_realpath(x_23, x_15);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static uint8_t _init_l_Lean_getBuiltinSearchPath___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = LEAN_IS_STAGE0;
return x_2;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean");
return x_1;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_2 = l_Lean_Syntax_formatStxAux___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getBuiltinSearchPath___closed__4;
x_2 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("stage1");
return x_1;
}
}
static lean_object* _init_l_Lean_getBuiltinSearchPath___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getBuiltinSearchPath___closed__5;
x_2 = l_Lean_getBuiltinSearchPath___closed__6;
x_3 = lean_string_append(x_1, x_2);
return x_3;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Lean_Syntax_formatStxAux___closed__3;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_getBuiltinSearchPath___closed__1;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = l_Lean_instInhabitedParserDescr___closed__1;
x_12 = lean_string_append(x_8, x_11);
x_13 = lean_string_append(x_12, x_5);
x_14 = l_Lean_getBuiltinSearchPath___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_5);
x_17 = l_Lean_getBuiltinSearchPath___closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_2, 0, x_19);
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = l_Lean_getBuiltinSearchPath___closed__7;
x_21 = lean_string_append(x_8, x_20);
x_22 = lean_string_append(x_21, x_5);
x_23 = l_Lean_getBuiltinSearchPath___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_5);
x_26 = l_Lean_getBuiltinSearchPath___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_32 = lean_string_append(x_29, x_31);
x_33 = l_Lean_Syntax_formatStxAux___closed__3;
x_34 = lean_string_append(x_32, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_getBuiltinSearchPath___closed__1;
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = l_Lean_instInhabitedParserDescr___closed__1;
x_38 = lean_string_append(x_34, x_37);
x_39 = lean_string_append(x_38, x_31);
x_40 = l_Lean_getBuiltinSearchPath___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_string_append(x_41, x_31);
x_43 = l_Lean_getBuiltinSearchPath___closed__3;
x_44 = lean_string_append(x_42, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_30);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = l_Lean_getBuiltinSearchPath___closed__7;
x_48 = lean_string_append(x_34, x_47);
x_49 = lean_string_append(x_48, x_31);
x_50 = l_Lean_getBuiltinSearchPath___closed__2;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_31);
x_53 = l_Lean_getBuiltinSearchPath___closed__3;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_35);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_30);
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
return x_2;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
lean_object* l_Lean_addSearchPathFromEnv_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_addSearchPathFromEnv_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addSearchPathFromEnv_match__1___rarg), 3, 0);
return x_2;
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
static lean_object* _init_l_Lean_addSearchPathFromEnv___closed__1() {
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_parseSearchPath(x_12, x_1);
lean_dec(x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_parseSearchPath(x_15, x_1);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
return x_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
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
lean_object* l_Lean_initSearchPath_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_initSearchPath_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_initSearchPath_match__1___rarg), 3, 0);
return x_2;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_searchPathRef;
x_10 = lean_st_ref_set(x_9, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = l_Lean_parseSearchPath(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_searchPathRef;
x_27 = lean_st_ref_set(x_26, x_25, x_2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_findOLean_maybeThisOne_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_findOLean_maybeThisOne_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_findOLean_maybeThisOne_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_findOLean_maybeThisOne___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_System_FilePath_parent(x_1);
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
x_1 = lean_mk_string("\nYou might need to open '");
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean_maybeThisOne___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' as a workspace in your editor");
return x_1;
}
}
lean_object* l_Lean_findOLean_maybeThisOne(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lean_instInhabitedParserDescr___closed__1;
x_5 = lean_string_append(x_4, x_2);
x_6 = lean_string_append(x_5, x_4);
x_7 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_4);
x_10 = l_Lean_Name_toString___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Name_toStringWithSep(x_10, x_1);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_string_append(x_12, x_4);
x_14 = lean_io_file_exists(x_13, x_3);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Lean_findOLean_maybeThisOne___lambda__1(x_2, x_1, x_18, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = l_Lean_findOLean_maybeThisOne___closed__1;
x_23 = lean_string_append(x_22, x_2);
lean_dec(x_2);
x_24 = l_Lean_findOLean_maybeThisOne___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_14, 0, x_26);
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_findOLean_maybeThisOne___closed__1;
x_29 = lean_string_append(x_28, x_2);
lean_dec(x_2);
x_30 = l_Lean_findOLean_maybeThisOne___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_findOLean_maybeThisOne___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_findOLean_maybeThisOne___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_IO_currentDir___at_Lean_findOLean___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_io_current_dir(x_1);
return x_2;
}
}
lean_object* l_Lean_findOLean___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_mk_string(".olean");
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown package '");
return x_1;
}
}
static lean_object* _init_l_Lean_findOLean___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_findOLean___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_findOLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_searchPathRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_findOLean___closed__1;
x_8 = l_Lean_SearchPath_findWithExt(x_5, x_7, x_1, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Name_getRoot(x_1);
x_12 = l_Lean_Name_toString___closed__1;
lean_inc(x_11);
x_13 = l_Lean_Name_toStringWithSep(x_12, x_11);
x_14 = l_Lean_findOLean___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Char_quote___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_io_current_dir(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_findOLean_maybeThisOne(x_11, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_findOLean___closed__3;
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
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
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
lean_dec(x_17);
lean_dec(x_11);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_8, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_9, 0);
lean_inc(x_41);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_41);
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 1);
lean_inc(x_42);
lean_dec(x_8);
x_43 = lean_ctor_get(x_9, 0);
lean_inc(x_43);
lean_dec(x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
return x_8;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l_Lean_findOLean___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findOLean___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
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
lean_object* l_Lean_moduleNameOfFileName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_moduleNameOfFileName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_moduleNameOfFileName_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_moduleNameOfFileName_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_moduleNameOfFileName_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_moduleNameOfFileName_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to convert file name '");
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' to module name, extension is missing");
return x_1;
}
}
lean_object* l_Lean_moduleNameOfFileName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; uint32_t x_11; 
x_5 = lean_string_length(x_1);
lean_inc(x_2);
x_6 = l_String_drop(x_2, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_get(x_6, x_7);
x_9 = l_System_FilePath_pathSeparator;
x_10 = x_8 == x_9;
x_11 = 46;
if (x_10 == 0)
{
lean_object* x_12; 
x_12 = l_String_revPosOf(x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_13 = l_Lean_moduleNameOfFileName___lambda__1___closed__1;
x_14 = lean_string_append(x_13, x_2);
lean_dec(x_2);
x_15 = l_Lean_moduleNameOfFileName___lambda__1___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_string_utf8_extract(x_6, x_7, x_19);
lean_dec(x_19);
lean_dec(x_6);
x_21 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_22 = l_String_splitOn(x_20, x_21);
x_23 = lean_box(0);
x_24 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_23, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = l_String_drop(x_6, x_26);
x_28 = l_String_revPosOf(x_27, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_29 = l_Lean_moduleNameOfFileName___lambda__1___closed__1;
x_30 = lean_string_append(x_29, x_2);
lean_dec(x_2);
x_31 = l_Lean_moduleNameOfFileName___lambda__1___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_string_utf8_extract(x_27, x_7, x_35);
lean_dec(x_35);
lean_dec(x_27);
x_37 = l___private_Lean_Util_Path_0__Lean_pathSep;
x_38 = l_String_splitOn(x_36, x_37);
x_39 = lean_box(0);
x_40 = l_List_foldl___at_Lean_moduleNameOfFileName___spec__1(x_39, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_4);
return x_41;
}
}
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input file '");
return x_1;
}
}
static lean_object* _init_l_Lean_moduleNameOfFileName___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' must be contained in root directory (");
return x_1;
}
}
lean_object* l_Lean_moduleNameOfFileName___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_realPathNormalized(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_String_isPrefixOf(x_6, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_moduleNameOfFileName___lambda__2___closed__1;
x_10 = lean_string_append(x_9, x_1);
lean_dec(x_1);
x_11 = l_Lean_moduleNameOfFileName___lambda__2___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_6);
lean_dec(x_6);
x_14 = l_prec_x28___x29___closed__7;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
x_17 = lean_box(0);
x_18 = l_Lean_moduleNameOfFileName___lambda__1(x_6, x_1, x_17, x_7);
lean_dec(x_6);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
x_21 = l_String_isPrefixOf(x_19, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = l_Lean_moduleNameOfFileName___lambda__2___closed__1;
x_23 = lean_string_append(x_22, x_1);
lean_dec(x_1);
x_24 = l_Lean_moduleNameOfFileName___lambda__2___closed__2;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_19);
lean_dec(x_19);
x_27 = l_prec_x28___x29___closed__7;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l_Lean_moduleNameOfFileName___lambda__1(x_19, x_1, x_31, x_20);
lean_dec(x_19);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* lean_module_name_of_file(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_realPathNormalized(x_1, x_3);
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
x_10 = l_Lean_moduleNameOfFileName___lambda__2(x_5, x_8, x_9);
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
x_18 = l_Lean_moduleNameOfFileName___lambda__2(x_15, x_17, x_16);
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
lean_object* l_Lean_moduleNameOfFileName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_moduleNameOfFileName___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Name(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_Path(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Util_Path_0__Lean_pathSep = _init_l___private_Lean_Util_Path_0__Lean_pathSep();
lean_mark_persistent(l___private_Lean_Util_Path_0__Lean_pathSep);
l_Lean_modPathToFilePath___closed__1 = _init_l_Lean_modPathToFilePath___closed__1();
lean_mark_persistent(l_Lean_modPathToFilePath___closed__1);
l_Lean_modPathToFilePath___closed__2 = _init_l_Lean_modPathToFilePath___closed__2();
lean_mark_persistent(l_Lean_modPathToFilePath___closed__2);
l_Lean_modPathToFilePath___closed__3 = _init_l_Lean_modPathToFilePath___closed__3();
lean_mark_persistent(l_Lean_modPathToFilePath___closed__3);
l_Lean_modPathToFilePath___closed__4 = _init_l_Lean_modPathToFilePath___closed__4();
lean_mark_persistent(l_Lean_modPathToFilePath___closed__4);
res = l_Lean_initFn____x40_Lean_Util_Path___hyg_199_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
l_Lean_getBuiltinSearchPath___closed__2 = _init_l_Lean_getBuiltinSearchPath___closed__2();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__2);
l_Lean_getBuiltinSearchPath___closed__3 = _init_l_Lean_getBuiltinSearchPath___closed__3();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__3);
l_Lean_getBuiltinSearchPath___closed__4 = _init_l_Lean_getBuiltinSearchPath___closed__4();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__4);
l_Lean_getBuiltinSearchPath___closed__5 = _init_l_Lean_getBuiltinSearchPath___closed__5();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__5);
l_Lean_getBuiltinSearchPath___closed__6 = _init_l_Lean_getBuiltinSearchPath___closed__6();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__6);
l_Lean_getBuiltinSearchPath___closed__7 = _init_l_Lean_getBuiltinSearchPath___closed__7();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__7);
l_Lean_addSearchPathFromEnv___closed__1 = _init_l_Lean_addSearchPathFromEnv___closed__1();
lean_mark_persistent(l_Lean_addSearchPathFromEnv___closed__1);
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
l_Lean_moduleNameOfFileName___lambda__1___closed__1 = _init_l_Lean_moduleNameOfFileName___lambda__1___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__1___closed__1);
l_Lean_moduleNameOfFileName___lambda__1___closed__2 = _init_l_Lean_moduleNameOfFileName___lambda__1___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__1___closed__2);
l_Lean_moduleNameOfFileName___lambda__2___closed__1 = _init_l_Lean_moduleNameOfFileName___lambda__2___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__2___closed__1);
l_Lean_moduleNameOfFileName___lambda__2___closed__2 = _init_l_Lean_moduleNameOfFileName___lambda__2___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___lambda__2___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
