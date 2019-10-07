// Lean compiler output
// Module: Init.Lean.Path
// Imports: Init.System.IO Init.System.FilePath Init.Data.Array.Default Init.Control.Combinators Init.Lean.Name
#include "runtime/lean.h"
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
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* l_Lean_getBuiltinSearchPath___closed__2;
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mmap___main___at_Lean_setSearchPath___spec__1(lean_object*, lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_IO_fileExists___at_Lean_findFile___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getSearchPathFromEnv___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_moduleNameOfFileName___closed__4;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* l_IO_realPath___at_Lean_realPathNormalized___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_setSearchPath(lean_object*, lean_object*);
lean_object* l_Lean_modNameToFileName(lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_findOLean___closed__1;
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__4;
lean_object* l_Lean_addRel___boxed(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_addRel___main(lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_System_FilePath_normalizePath(lean_object*);
lean_object* l_IO_Prim_Ref_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setSearchPathFromString(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Path_2__searchPathSep___closed__1;
lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* l_Array_mkEmpty(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_findLeanFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
extern uint32_t l_System_FilePath_searchPathSeparator;
lean_object* l_Lean_getSearchPathFromEnv___closed__2;
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findFile(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_file_exists(lean_object*, lean_object*);
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
lean_object* l_Lean_modNameToFileName___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_repr___at_Lean_findAtSearchPath___spec__2(lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__1;
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*);
lean_object* l_String_drop(lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__1;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_findLeanFile___closed__2;
lean_object* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_findLeanFile(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__2;
lean_object* l_Lean_searchPathRef;
lean_object* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_modNameToFileName___main(lean_object*);
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_mkSearchPathRef___closed__1;
lean_object* l_IO_fileExists___at_Lean_findFile___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_IO_Prim_mkRef(lean_object*, lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(uint8_t, lean_object*);
lean_object* l_Lean_addRel___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_modNameToFileName___main___boxed(lean_object*);
lean_object* l___private_Init_Lean_Path_2__searchPathSep;
lean_object* l_Lean_moduleNameOfFileName___closed__1;
lean_object* l_String_split(lean_object*, lean_object*);
lean_object* l_IO_Prim_Ref_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findAtSearchPath(lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
lean_object* l_Lean_moduleNameOfFileName___closed__3;
lean_object* l_Array_size(lean_object*, lean_object*);
extern uint32_t l_System_FilePath_extSeparator;
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getSearchPathFromEnv(lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Path_1__pathSep;
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* l___private_Init_Lean_Path_1__pathSep___closed__1;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findLeanFile___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_lean(lean_object*, lean_object*);
lean_object* l_Lean_addRel(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_mkSearchPathRef(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__3;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* _init_l___private_Init_Lean_Path_1__pathSep___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Path_1__pathSep() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Init_Lean_Path_1__pathSep___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Path_2__searchPathSep___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_searchPathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Path_2__searchPathSep() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Init_Lean_Path_2__searchPathSep___closed__1;
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
lean_object* _init_l_Lean_mkSearchPathRef___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_mkSearchPathRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_realPathNormalized(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_mkSearchPathRef___closed__1;
x_8 = lean_array_push(x_7, x_5);
x_9 = lean_io_mk_ref(x_8, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_mkSearchPathRef___closed__1;
x_15 = lean_array_push(x_14, x_10);
x_16 = lean_io_mk_ref(x_15, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_List_mmap___main___at_Lean_setSearchPath___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
x_5 = lean_box(0);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_realPathNormalized(x_10, x_2);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_box(0);
lean_ctor_set(x_12, 0, x_15);
x_16 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_free_object(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_31);
lean_ctor_set(x_1, 0, x_26);
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_26);
lean_free_object(x_1);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_37 = x_30;
} else {
 lean_dec_ref(x_30);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_1);
lean_dec(x_11);
x_39 = !lean_is_exclusive(x_12);
if (x_39 == 0)
{
return x_12;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_12, 0);
x_41 = lean_ctor_get(x_12, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_12);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_1);
x_45 = l_Lean_realPathNormalized(x_43, x_2);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
x_51 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_44, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_46);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_44);
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_63 = x_45;
} else {
 lean_dec_ref(x_45);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
lean_object* l_Lean_setSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_List_redLength___main___rarg(x_5);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___main___rarg(x_5, x_8);
x_10 = l_Lean_searchPathRef;
x_11 = lean_io_ref_set(x_10, x_9, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_List_redLength___main___rarg(x_12);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_12, x_17);
x_19 = l_Lean_searchPathRef;
x_20 = lean_io_ref_set(x_19, x_18, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_setSearchPathFromString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l___private_Init_Lean_Path_2__searchPathSep;
x_4 = l_String_split(x_1, x_3);
x_5 = l_Lean_setSearchPath(x_4, x_2);
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
lean_ctor_set(x_2, 0, x_5);
x_6 = l_System_FilePath_dirName(x_4);
x_7 = lean_io_realpath(x_6, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_System_FilePath_dirName(x_8);
x_13 = lean_io_realpath(x_12, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
return x_3;
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
x_1 = lean_mk_string("library");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__4() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
lean_ctor_set(x_2, 0, x_5);
x_6 = l___private_Init_Lean_Path_1__pathSep;
x_7 = lean_string_append(x_4, x_6);
x_8 = l_Lean_getBuiltinSearchPath___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_6);
x_11 = l_Lean_getBuiltinSearchPath___closed__2;
lean_inc(x_10);
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_io_is_dir(x_12, x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_13, 0, x_5);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_17 = l_Lean_getBuiltinSearchPath___closed__3;
x_18 = lean_string_append(x_10, x_17);
x_19 = lean_string_append(x_18, x_6);
x_20 = l_Lean_getBuiltinSearchPath___closed__4;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_6);
x_23 = lean_string_append(x_22, x_11);
x_24 = lean_io_is_dir(x_23, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_23);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_24, 0, x_29);
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_24, 0);
lean_dec(x_34);
lean_ctor_set(x_24, 0, x_5);
x_35 = l_Lean_realPathNormalized(x_23, x_24);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_dec(x_24);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_realPathNormalized(x_23, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_23);
x_62 = !lean_is_exclusive(x_24);
if (x_62 == 0)
{
return x_24;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_24, 0);
x_64 = lean_ctor_get(x_24, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_24);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_10);
x_66 = l_Lean_realPathNormalized(x_12, x_13);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_13, 0);
x_81 = lean_ctor_get(x_13, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_13);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_unbox(x_80);
lean_dec(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_12);
x_84 = l_Lean_getBuiltinSearchPath___closed__3;
x_85 = lean_string_append(x_10, x_84);
x_86 = lean_string_append(x_85, x_6);
x_87 = l_Lean_getBuiltinSearchPath___closed__4;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_string_append(x_88, x_6);
x_90 = lean_string_append(x_89, x_11);
x_91 = lean_io_is_dir(x_90, x_82);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_99 = x_91;
} else {
 lean_dec_ref(x_91);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_realPathNormalized(x_90, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_90);
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_91, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_114 = x_91;
} else {
 lean_dec_ref(x_91);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec(x_10);
x_116 = l_Lean_realPathNormalized(x_12, x_82);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_119)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_119;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_118);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_116, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_116, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_12);
lean_dec(x_10);
x_127 = !lean_is_exclusive(x_13);
if (x_127 == 0)
{
return x_13;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_13, 0);
x_129 = lean_ctor_get(x_13, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_13);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_131 = lean_ctor_get(x_2, 0);
x_132 = lean_ctor_get(x_2, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_2);
x_133 = lean_box(0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
x_135 = l___private_Init_Lean_Path_1__pathSep;
x_136 = lean_string_append(x_131, x_135);
x_137 = l_Lean_getBuiltinSearchPath___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_135);
x_140 = l_Lean_getBuiltinSearchPath___closed__2;
lean_inc(x_139);
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_io_is_dir(x_141, x_134);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_133);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_unbox(x_143);
lean_dec(x_143);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_141);
x_148 = l_Lean_getBuiltinSearchPath___closed__3;
x_149 = lean_string_append(x_139, x_148);
x_150 = lean_string_append(x_149, x_135);
x_151 = l_Lean_getBuiltinSearchPath___closed__4;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_string_append(x_152, x_135);
x_154 = lean_string_append(x_153, x_140);
x_155 = lean_io_is_dir(x_154, x_146);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_unbox(x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_154);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = lean_box(0);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_133);
lean_ctor_set(x_164, 1, x_162);
x_165 = l_Lean_realPathNormalized(x_154, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_167);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_174 = x_165;
} else {
 lean_dec_ref(x_165);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_154);
x_176 = lean_ctor_get(x_155, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_155, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_178 = x_155;
} else {
 lean_dec_ref(x_155);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; 
lean_dec(x_139);
x_180 = l_Lean_realPathNormalized(x_141, x_146);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_181);
lean_ctor_set(x_185, 1, x_184);
if (lean_is_scalar(x_183)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_183;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_182);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_180, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_189 = x_180;
} else {
 lean_dec_ref(x_180);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_141);
lean_dec(x_139);
x_191 = lean_ctor_get(x_142, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_142, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_193 = x_142;
} else {
 lean_dec_ref(x_142);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_2);
if (x_195 == 0)
{
return x_2;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_2, 0);
x_197 = lean_ctor_get(x_2, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_2);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
}
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getSearchPathFromEnv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("LEAN_PATH");
return x_1;
}
}
lean_object* _init_l_Lean_getSearchPathFromEnv___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_getSearchPathFromEnv(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getSearchPathFromEnv___closed__1;
x_3 = lean_io_getenv(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = l_Lean_getSearchPathFromEnv___closed__2;
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_getSearchPathFromEnv___closed__2;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = l___private_Init_Lean_Path_2__searchPathSep;
x_15 = l_String_split(x_13, x_14);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l___private_Init_Lean_Path_2__searchPathSep;
x_19 = l_String_split(x_17, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(x_1, x_2);
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
x_3 = l_Lean_getSearchPathFromEnv(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_getBuiltinSearchPath(x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_ctor_set(x_7, 0, x_6);
x_10 = l_List_append___rarg(x_5, x_9);
x_11 = l_Lean_setSearchPath(x_10, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_List_append___rarg(x_5, x_12);
x_16 = l_Lean_setSearchPath(x_15, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_getBuiltinSearchPath(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_List_append___rarg(x_21, x_26);
x_31 = l_Lean_setSearchPath(x_30, x_29);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_3);
if (x_36 == 0)
{
return x_3;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lean_setSearchPathFromString(x_40, x_2);
return x_41;
}
}
}
lean_object* l_IO_fileExists___at_Lean_findFile___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_extSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Default");
return x_1;
}
}
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_4, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_23 = lean_array_fget(x_3, x_4);
x_24 = l___private_Init_Lean_Path_1__pathSep;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_2);
x_49 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
lean_inc(x_26);
x_50 = lean_string_append(x_26, x_49);
x_51 = lean_string_append(x_50, x_1);
x_52 = lean_io_file_exists(x_51, x_5);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
x_27 = x_56;
x_28 = x_55;
goto block_48;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_51);
x_27 = x_58;
x_28 = x_57;
goto block_48;
}
}
else
{
uint8_t x_59; 
lean_dec(x_51);
lean_dec(x_26);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
block_48:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_string_append(x_26, x_24);
x_32 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_1);
x_37 = lean_io_file_exists(x_36, x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_36);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_box(0);
x_6 = x_41;
x_7 = x_40;
goto block_14;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_6 = x_43;
x_7 = x_42;
goto block_14;
}
}
else
{
uint8_t x_44; 
lean_dec(x_36);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_dec(x_26);
x_6 = x_27;
x_7 = x_28;
goto block_14;
}
}
}
block_14:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
}
}
}
lean_object* l_Lean_findFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_System_FilePath_normalizePath(x_1);
x_5 = l_Lean_searchPathRef;
x_6 = lean_io_ref_get(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
lean_ctor_set(x_6, 0, x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_2, x_4, x_8, x_10, x_6);
lean_dec(x_8);
lean_dec(x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_2, x_4, x_12, x_16, x_15);
lean_dec(x_12);
lean_dec(x_4);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_IO_fileExists___at_Lean_findFile___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_fileExists___at_Lean_findFile___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_findFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_modNameToFileName___main(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_modNameToFileName___main(x_3);
x_8 = l___private_Init_Lean_Path_1__pathSep;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_4);
return x_10;
}
else
{
lean_inc(x_4);
return x_4;
}
}
default: 
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
x_1 = x_11;
goto _start;
}
}
}
}
lean_object* l_Lean_modNameToFileName___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modNameToFileName___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_modNameToFileName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modNameToFileName___main(x_1);
return x_2;
}
}
lean_object* l_Lean_modNameToFileName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_modNameToFileName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_addRel___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Lean_addRel___main(x_1, x_6);
lean_dec(x_6);
x_8 = l___private_Init_Lean_Path_1__pathSep;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_getBuiltinSearchPath___closed__1;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_addRel___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_addRel___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_addRel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_addRel___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_addRel___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_addRel(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* _init_l_Lean_findLeanFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("module '");
return x_1;
}
}
lean_object* _init_l_Lean_findLeanFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' not found");
return x_1;
}
}
lean_object* l_Lean_findLeanFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_modNameToFileName___main(x_1);
x_5 = l_Lean_findFile(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = l_Lean_findLeanFile___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_findLeanFile___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = l_Lean_Name_toString___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_1);
x_18 = l_Lean_findLeanFile___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_findLeanFile___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_15);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_box(0);
lean_ctor_set(x_5, 0, x_26);
x_27 = l_Lean_realPathNormalized(x_25, x_5);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = l_Lean_realPathNormalized(x_29, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_findLeanFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findLeanFile(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_findOLean___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("olean");
return x_1;
}
}
lean_object* l_Lean_findOLean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_findOLean___closed__1;
x_4 = l_Lean_findLeanFile(x_1, x_3, x_2);
return x_4;
}
}
lean_object* lean_find_lean(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_getBuiltinSearchPath___closed__4;
x_4 = l_Lean_findLeanFile(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_String_isPrefixOf(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
}
}
}
lean_object* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_String_quote(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_1, x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
x_11 = l_String_splitAux___main___closed__1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_String_quote(x_12);
x_15 = 0;
x_16 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_15, x_13);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
lean_object* l_List_repr___at_Lean_findAtSearchPath___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_findAtSearchPath___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("file '");
return x_1;
}
}
lean_object* _init_l_Lean_findAtSearchPath___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' not in the search path ");
return x_1;
}
}
lean_object* l_Lean_findAtSearchPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_realPathNormalized(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_searchPathRef;
x_8 = lean_io_ref_get(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_5, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_findAtSearchPath___closed__1;
x_14 = lean_string_append(x_13, x_5);
lean_dec(x_5);
x_15 = l_Lean_findAtSearchPath___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_18 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
lean_ctor_set(x_8, 0, x_20);
return x_8;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_5, x_21, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = l_Lean_findAtSearchPath___closed__1;
x_26 = lean_string_append(x_25, x_5);
lean_dec(x_5);
x_27 = l_Lean_findAtSearchPath___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Array_toList___rarg(x_21);
lean_dec(x_21);
x_30 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_29);
x_31 = lean_string_append(x_28, x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_5);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_22);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_3);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_searchPathRef;
x_44 = lean_io_ref_get(x_43, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_39, x_45, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = l_Lean_findAtSearchPath___closed__1;
x_51 = lean_string_append(x_50, x_39);
lean_dec(x_39);
x_52 = l_Lean_findAtSearchPath___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_55 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_54);
x_56 = lean_string_append(x_53, x_55);
lean_dec(x_55);
if (lean_is_scalar(x_47)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_47;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_46);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
lean_dec(x_39);
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
if (lean_is_scalar(x_47)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_47;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_46);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_39);
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_62 = x_44;
} else {
 lean_dec_ref(x_44);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_3);
if (x_64 == 0)
{
return x_3;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_3, 0);
x_66 = lean_ctor_get(x_3, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_3);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
lean_object* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string("failed to convert file '");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' to module name, path is not a prefix of the given file");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' to module name, extension is missing");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' to module name, module name '");
return x_1;
}
}
lean_object* _init_l_Lean_moduleNameOfFileName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' resolves to '");
return x_1;
}
}
lean_object* lean_module_name_of_file(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_Lean_findAtSearchPath(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
x_7 = l_Lean_realPathNormalized(x_1, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; uint32_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_string_length(x_5);
x_12 = l_String_drop(x_8, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_get(x_12, x_13);
x_15 = l_System_FilePath_pathSeparator;
x_16 = x_14 == x_15;
x_17 = l___private_Init_Lean_Path_1__pathSep;
x_18 = lean_string_append(x_5, x_17);
if (x_16 == 0)
{
x_19 = x_12;
goto block_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_String_drop(x_12, x_82);
lean_dec(x_12);
x_19 = x_83;
goto block_81;
}
block_81:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_dec_eq(x_20, x_8);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_22 = l_Lean_moduleNameOfFileName___closed__1;
x_23 = lean_string_append(x_22, x_8);
lean_dec(x_8);
x_24 = l_Lean_moduleNameOfFileName___closed__2;
x_25 = lean_string_append(x_23, x_24);
if (lean_is_scalar(x_10)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_10;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
else
{
uint32_t x_27; lean_object* x_28; 
x_27 = 46;
x_28 = l_String_revPosOf(x_19, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_19);
x_29 = l_Lean_moduleNameOfFileName___closed__1;
x_30 = lean_string_append(x_29, x_8);
lean_dec(x_8);
x_31 = l_Lean_moduleNameOfFileName___closed__3;
x_32 = lean_string_append(x_30, x_31);
if (lean_is_scalar(x_10)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_10;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
if (lean_is_scalar(x_10)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_10;
}
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_9);
x_36 = lean_string_utf8_extract(x_19, x_13, x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_34, x_37);
lean_dec(x_34);
x_39 = lean_string_utf8_byte_size(x_19);
x_40 = lean_string_utf8_extract(x_19, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_19);
x_41 = l_String_split(x_36, x_17);
x_42 = lean_box(0);
x_43 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_42, x_41);
lean_inc(x_43);
x_44 = l_Lean_findLeanFile(x_43, x_40, x_35);
lean_dec(x_40);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_string_dec_eq(x_8, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = l_Lean_moduleNameOfFileName___closed__1;
x_49 = lean_string_append(x_48, x_8);
lean_dec(x_8);
x_50 = l_Lean_moduleNameOfFileName___closed__4;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_43);
x_54 = lean_string_append(x_51, x_53);
lean_dec(x_53);
x_55 = l_Lean_moduleNameOfFileName___closed__5;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_46);
lean_dec(x_46);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean_string_append(x_57, x_58);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_59);
return x_44;
}
else
{
lean_dec(x_46);
lean_dec(x_8);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_62 = lean_string_dec_eq(x_8, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_63 = l_Lean_moduleNameOfFileName___closed__1;
x_64 = lean_string_append(x_63, x_8);
lean_dec(x_8);
x_65 = l_Lean_moduleNameOfFileName___closed__4;
x_66 = lean_string_append(x_64, x_65);
x_67 = l_Lean_Name_toString___closed__1;
x_68 = l_Lean_Name_toStringWithSep___main(x_67, x_43);
x_69 = lean_string_append(x_66, x_68);
lean_dec(x_68);
x_70 = l_Lean_moduleNameOfFileName___closed__5;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_string_append(x_71, x_60);
lean_dec(x_60);
x_73 = l_Char_HasRepr___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_61);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_60);
lean_dec(x_8);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_43);
lean_ctor_set(x_76, 1, x_61);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_43);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_44);
if (x_77 == 0)
{
return x_44;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_44, 0);
x_79 = lean_ctor_get(x_44, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_44);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_7);
if (x_84 == 0)
{
return x_7;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_7, 0);
x_86 = lean_ctor_get(x_7, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_7);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_3, 0);
x_89 = lean_ctor_get(x_3, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_3);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_realPathNormalized(x_1, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint32_t x_99; uint32_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_string_length(x_88);
x_97 = l_String_drop(x_93, x_96);
lean_dec(x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_string_utf8_get(x_97, x_98);
x_100 = l_System_FilePath_pathSeparator;
x_101 = x_99 == x_100;
x_102 = l___private_Init_Lean_Path_1__pathSep;
x_103 = lean_string_append(x_88, x_102);
if (x_101 == 0)
{
x_104 = x_97;
goto block_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(1u);
x_154 = l_String_drop(x_97, x_153);
lean_dec(x_97);
x_104 = x_154;
goto block_152;
}
block_152:
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_string_dec_eq(x_105, x_93);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_107 = l_Lean_moduleNameOfFileName___closed__1;
x_108 = lean_string_append(x_107, x_93);
lean_dec(x_93);
x_109 = l_Lean_moduleNameOfFileName___closed__2;
x_110 = lean_string_append(x_108, x_109);
if (lean_is_scalar(x_95)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_95;
 lean_ctor_set_tag(x_111, 1);
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_94);
return x_111;
}
else
{
uint32_t x_112; lean_object* x_113; 
x_112 = 46;
x_113 = l_String_revPosOf(x_104, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_104);
x_114 = l_Lean_moduleNameOfFileName___closed__1;
x_115 = lean_string_append(x_114, x_93);
lean_dec(x_93);
x_116 = l_Lean_moduleNameOfFileName___closed__3;
x_117 = lean_string_append(x_115, x_116);
if (lean_is_scalar(x_95)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_95;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_94);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
lean_dec(x_113);
if (lean_is_scalar(x_95)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_95;
}
lean_ctor_set(x_120, 0, x_90);
lean_ctor_set(x_120, 1, x_94);
x_121 = lean_string_utf8_extract(x_104, x_98, x_119);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_119, x_122);
lean_dec(x_119);
x_124 = lean_string_utf8_byte_size(x_104);
x_125 = lean_string_utf8_extract(x_104, x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_104);
x_126 = l_String_split(x_121, x_102);
x_127 = lean_box(0);
x_128 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_127, x_126);
lean_inc(x_128);
x_129 = l_Lean_findLeanFile(x_128, x_125, x_120);
lean_dec(x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_string_dec_eq(x_93, x_130);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_134 = l_Lean_moduleNameOfFileName___closed__1;
x_135 = lean_string_append(x_134, x_93);
lean_dec(x_93);
x_136 = l_Lean_moduleNameOfFileName___closed__4;
x_137 = lean_string_append(x_135, x_136);
x_138 = l_Lean_Name_toString___closed__1;
x_139 = l_Lean_Name_toStringWithSep___main(x_138, x_128);
x_140 = lean_string_append(x_137, x_139);
lean_dec(x_139);
x_141 = l_Lean_moduleNameOfFileName___closed__5;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_string_append(x_142, x_130);
lean_dec(x_130);
x_144 = l_Char_HasRepr___closed__1;
x_145 = lean_string_append(x_143, x_144);
if (lean_is_scalar(x_132)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_132;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_131);
return x_146;
}
else
{
lean_object* x_147; 
lean_dec(x_130);
lean_dec(x_93);
if (lean_is_scalar(x_132)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_132;
}
lean_ctor_set(x_147, 0, x_128);
lean_ctor_set(x_147, 1, x_131);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_128);
lean_dec(x_93);
x_148 = lean_ctor_get(x_129, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_129, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_150 = x_129;
} else {
 lean_dec_ref(x_129);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_88);
x_155 = lean_ctor_get(x_92, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_92, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_157 = x_92;
} else {
 lean_dec_ref(x_92);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_3);
if (x_159 == 0)
{
return x_3;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_3, 0);
x_161 = lean_ctor_get(x_3, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_3);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_System_FilePath(lean_object*);
lean_object* initialize_Init_Data_Array_Default(lean_object*);
lean_object* initialize_Init_Control_Combinators(lean_object*);
lean_object* initialize_Init_Lean_Name(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Path(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_System_IO(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_System_FilePath(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Data_Array_Default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Control_Combinators(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_Init_Lean_Name(w);
if (lean_io_result_is_error(w)) return w;
l___private_Init_Lean_Path_1__pathSep___closed__1 = _init_l___private_Init_Lean_Path_1__pathSep___closed__1();
lean_mark_persistent(l___private_Init_Lean_Path_1__pathSep___closed__1);
l___private_Init_Lean_Path_1__pathSep = _init_l___private_Init_Lean_Path_1__pathSep();
lean_mark_persistent(l___private_Init_Lean_Path_1__pathSep);
l___private_Init_Lean_Path_2__searchPathSep___closed__1 = _init_l___private_Init_Lean_Path_2__searchPathSep___closed__1();
lean_mark_persistent(l___private_Init_Lean_Path_2__searchPathSep___closed__1);
l___private_Init_Lean_Path_2__searchPathSep = _init_l___private_Init_Lean_Path_2__searchPathSep();
lean_mark_persistent(l___private_Init_Lean_Path_2__searchPathSep);
l_Lean_mkSearchPathRef___closed__1 = _init_l_Lean_mkSearchPathRef___closed__1();
lean_mark_persistent(l_Lean_mkSearchPathRef___closed__1);
w = l_Lean_mkSearchPathRef(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_searchPathRef = lean_io_result_get_value(w);
lean_mark_persistent(l_Lean_searchPathRef);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__1);
l_Lean_getBuiltinSearchPath___closed__2 = _init_l_Lean_getBuiltinSearchPath___closed__2();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__2);
l_Lean_getBuiltinSearchPath___closed__3 = _init_l_Lean_getBuiltinSearchPath___closed__3();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__3);
l_Lean_getBuiltinSearchPath___closed__4 = _init_l_Lean_getBuiltinSearchPath___closed__4();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__4);
l_Lean_getSearchPathFromEnv___closed__1 = _init_l_Lean_getSearchPathFromEnv___closed__1();
lean_mark_persistent(l_Lean_getSearchPathFromEnv___closed__1);
l_Lean_getSearchPathFromEnv___closed__2 = _init_l_Lean_getSearchPathFromEnv___closed__2();
lean_mark_persistent(l_Lean_getSearchPathFromEnv___closed__2);
l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1 = _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1();
lean_mark_persistent(l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1);
l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2 = _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2();
lean_mark_persistent(l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2);
l_Lean_findLeanFile___closed__1 = _init_l_Lean_findLeanFile___closed__1();
lean_mark_persistent(l_Lean_findLeanFile___closed__1);
l_Lean_findLeanFile___closed__2 = _init_l_Lean_findLeanFile___closed__2();
lean_mark_persistent(l_Lean_findLeanFile___closed__2);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean_mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findAtSearchPath___closed__1 = _init_l_Lean_findAtSearchPath___closed__1();
lean_mark_persistent(l_Lean_findAtSearchPath___closed__1);
l_Lean_findAtSearchPath___closed__2 = _init_l_Lean_findAtSearchPath___closed__2();
lean_mark_persistent(l_Lean_findAtSearchPath___closed__2);
l_Lean_moduleNameOfFileName___closed__1 = _init_l_Lean_moduleNameOfFileName___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__1);
l_Lean_moduleNameOfFileName___closed__2 = _init_l_Lean_moduleNameOfFileName___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__2);
l_Lean_moduleNameOfFileName___closed__3 = _init_l_Lean_moduleNameOfFileName___closed__3();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__3);
l_Lean_moduleNameOfFileName___closed__4 = _init_l_Lean_moduleNameOfFileName___closed__4();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__4);
l_Lean_moduleNameOfFileName___closed__5 = _init_l_Lean_moduleNameOfFileName___closed__5();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__5);
return w;
}
#ifdef __cplusplus
}
#endif
