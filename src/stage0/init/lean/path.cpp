// Lean compiler output
// Module: init.lean.path
// Imports: init.system.io init.system.filepath init.data.array.default init.control.combinators init.lean.name
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_String_revPosOf(obj*, uint32);
obj* l_Lean_getBuiltinSearchPath___closed__2;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_List_mmap___main___at_Lean_setSearchPath___spec__1(obj*, obj*);
obj* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(obj*);
extern "C" obj* lean_io_realpath(obj*, obj*);
obj* l_IO_fileExists___at_Lean_findFile___spec__1(obj*, obj*);
obj* l_Lean_moduleNameOfFileName___closed__5;
extern "C" obj* lean_nat_sub(obj*, obj*);
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(obj*, obj*);
obj* l_Lean_getSearchPathFromEnv___closed__1;
obj* l_Array_mkArray(obj*, obj*, obj*);
extern obj* l_List_repr___rarg___closed__3;
obj* l_Lean_moduleNameOfFileName___closed__4;
obj* l_Lean_findOLean(obj*, obj*);
obj* l_IO_realPath___at_Lean_realPathNormalized___spec__1(obj*, obj*);
obj* l_Lean_setSearchPath(obj*, obj*);
obj* l_Lean_modNameToFileName(obj*);
uint8 l_String_isPrefixOf(obj*, obj*);
obj* l_Lean_findOLean___closed__1;
extern "C" obj* lean_io_is_dir(obj*, obj*);
extern "C" obj* lean_io_app_dir(obj*);
obj* l_Lean_getBuiltinSearchPath___closed__4;
obj* l_Lean_addRel___boxed(obj*, obj*);
obj* l_List_toArrayAux___main___rarg(obj*, obj*);
obj* l___private_init_lean_path_2__searchPathSep;
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_addRel___main(obj*, obj*);
obj* l_List_redLength___main___rarg(obj*);
obj* l_System_FilePath_normalizePath(obj*);
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_setSearchPathFromString(obj*, obj*);
obj* l_Lean_moduleNameOfFileName___closed__2;
obj* l_Array_mkEmpty(obj*, obj*);
extern "C" obj* lean_string_push(obj*, uint32);
obj* l_Lean_findLeanFile___boxed(obj*, obj*, obj*);
obj* l_Array_toList___rarg(obj*);
extern "C" obj* lean_io_getenv(obj*, obj*);
extern obj* l_List_repr___rarg___closed__2;
extern uint32 l_System_FilePath_searchPathSeparator;
obj* l_Lean_getSearchPathFromEnv___closed__2;
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_findFile(obj*, obj*, obj*);
extern "C" obj* lean_io_file_exists(obj*, obj*);
obj* l_Lean_realPathNormalized(obj*, obj*);
obj* l_Lean_modNameToFileName___boxed(obj*);
extern "C" obj* lean_string_append(obj*, obj*);
obj* l_List_repr___at_Lean_findAtSearchPath___spec__2(obj*);
obj* l_Lean_findAtSearchPath___closed__1;
extern obj* l_List_reprAux___main___rarg___closed__1;
obj* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(obj*);
extern "C" uint8 lean_nat_dec_lt(obj*, obj*);
extern "C" obj* lean_module_name_of_file(obj*, obj*);
obj* l_String_drop(obj*, obj*);
extern obj* l_Char_HasRepr___closed__1;
obj* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3___boxed(obj*, obj*);
obj* l_System_FilePath_dirName(obj*);
obj* l_Lean_getBuiltinSearchPath___closed__1;
obj* l_List_append___rarg(obj*, obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(obj*, obj*);
extern "C" obj* lean_nat_add(obj*, obj*);
obj* l_Lean_findLeanFile___closed__2;
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1___boxed(obj*, obj*);
obj* l_Lean_findLeanFile(obj*, obj*, obj*);
extern "C" uint8 lean_nat_dec_eq(obj*, obj*);
obj* l_Lean_findAtSearchPath___closed__2;
obj* l_Lean_searchPathRef;
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(obj*, obj*);
obj* l_Lean_modNameToFileName___main(obj*);
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(obj*, obj*);
extern "C" uint32 lean_string_utf8_get(obj*, obj*);
obj* l___private_init_lean_path_1__pathSep___closed__1;
obj* l_IO_fileExists___at_Lean_findFile___spec__1___boxed(obj*, obj*);
extern "C" uint8 lean_string_dec_eq(obj*, obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(uint8, obj*);
obj* l_Lean_addRel___main___boxed(obj*, obj*);
obj* l_Lean_modNameToFileName___main___boxed(obj*);
obj* l_Lean_moduleNameOfFileName___closed__1;
obj* l_String_split(obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l_Lean_findAtSearchPath(obj*, obj*);
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
obj* l_Lean_moduleNameOfFileName___closed__3;
obj* l___private_init_lean_path_2__searchPathSep___closed__1;
obj* l_Array_size(obj*, obj*);
extern uint32 l_System_FilePath_extSeparator;
obj* l___private_init_lean_path_1__pathSep;
obj* l_Lean_findFile___boxed(obj*, obj*, obj*);
obj* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(obj*, obj*, obj*);
obj* l_Lean_getSearchPathFromEnv(obj*);
extern "C" obj* lean_init_search_path(obj*, obj*);
extern uint32 l_System_FilePath_pathSeparator;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
extern "C" obj* lean_string_utf8_extract(obj*, obj*, obj*);
obj* l_Lean_findLeanFile___closed__1;
extern "C" obj* lean_string_utf8_byte_size(obj*);
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_find_lean(obj*, obj*);
obj* l_Lean_addRel(obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_mkSearchPathRef(obj*);
obj* l_Lean_getBuiltinSearchPath___closed__3;
extern obj* l_List_repr___rarg___closed__1;
obj* l_Lean_getBuiltinSearchPath(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1___boxed(obj*, obj*, obj*);
extern "C" obj* lean_string_length(obj*);
obj* _init_l___private_init_lean_path_1__pathSep___closed__1() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_path_1__pathSep() {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_path_1__pathSep___closed__1;
return x_1;
}
}
obj* _init_l___private_init_lean_path_2__searchPathSep___closed__1() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_searchPathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_path_2__searchPathSep() {
_start:
{
obj* x_1; 
x_1 = l___private_init_lean_path_2__searchPathSep___closed__1;
return x_1;
}
}
obj* l_IO_realPath___at_Lean_realPathNormalized___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
obj* l_Lean_realPathNormalized(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = l_System_FilePath_normalizePath(x_5);
lean::cnstr_set(x_3, 0, x_6);
return x_3;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::inc(x_7);
lean::dec(x_3);
x_9 = l_System_FilePath_normalizePath(x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
}
obj* l_Lean_mkSearchPathRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = l_Lean_realPathNormalized(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean_mk_array(x_7, x_5);
x_9 = lean_io_mk_ref(x_8, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_3, 0);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_3);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean_mk_array(x_14, x_10);
x_16 = lean_io_mk_ref(x_15, x_13);
return x_16;
}
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_3);
if (x_17 == 0)
{
return x_3;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_3, 0);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
}
obj* l_List_mmap___main___at_Lean_setSearchPath___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
lean::dec(x_4);
x_5 = lean::box(0);
lean::cnstr_set(x_2, 0, x_5);
return x_2;
}
else
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
}
else
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_1);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
x_11 = lean::cnstr_get(x_1, 1);
x_12 = l_Lean_realPathNormalized(x_10, x_2);
if (lean::obj_tag(x_12) == 0)
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = lean::box(0);
lean::cnstr_set(x_12, 0, x_15);
x_16 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_11, x_12);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; 
x_18 = lean::cnstr_get(x_16, 0);
lean::cnstr_set(x_1, 1, x_18);
lean::cnstr_set(x_1, 0, x_14);
lean::cnstr_set(x_16, 0, x_1);
return x_16;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_16, 0);
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_16);
lean::cnstr_set(x_1, 1, x_19);
lean::cnstr_set(x_1, 0, x_14);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8 x_22; 
lean::dec(x_14);
lean::free_heap_obj(x_1);
x_22 = !lean::is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_16, 0);
x_24 = lean::cnstr_get(x_16, 1);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_16);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_12, 0);
x_27 = lean::cnstr_get(x_12, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_12);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
x_30 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_11, x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_30, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_33 = x_30;
} else {
 lean::dec_ref(x_30);
 x_33 = lean::box(0);
}
lean::cnstr_set(x_1, 1, x_31);
lean::cnstr_set(x_1, 0, x_26);
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_32);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_26);
lean::free_heap_obj(x_1);
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_37 = x_30;
} else {
 lean::dec_ref(x_30);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8 x_39; 
lean::free_heap_obj(x_1);
lean::dec(x_11);
x_39 = !lean::is_exclusive(x_12);
if (x_39 == 0)
{
return x_12;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_12, 0);
x_41 = lean::cnstr_get(x_12, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_12);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_1, 0);
x_44 = lean::cnstr_get(x_1, 1);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_1);
x_45 = l_Lean_realPathNormalized(x_43, x_2);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_48 = x_45;
} else {
 lean::dec_ref(x_45);
 x_48 = lean::box(0);
}
x_49 = lean::box(0);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
x_51 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_44, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_54 = x_51;
} else {
 lean::dec_ref(x_51);
 x_54 = lean::box(0);
}
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_46);
lean::cnstr_set(x_55, 1, x_52);
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_46);
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_51, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_59 = x_51;
} else {
 lean::dec_ref(x_51);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_44);
x_61 = lean::cnstr_get(x_45, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_45, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_63 = x_45;
} else {
 lean::dec_ref(x_45);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
lean::cnstr_set(x_64, 1, x_62);
return x_64;
}
}
}
}
}
obj* l_Lean_setSearchPath(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_List_mmap___main___at_Lean_setSearchPath___spec__1(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_List_redLength___main___rarg(x_5);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean::dec(x_7);
x_9 = l_List_toArrayAux___main___rarg(x_5, x_8);
x_10 = l_Lean_searchPathRef;
x_11 = lean_io_ref_set(x_10, x_9, x_3);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_3, 0);
x_13 = lean::cnstr_get(x_3, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_3);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = l_List_redLength___main___rarg(x_12);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean::dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_12, x_17);
x_19 = l_Lean_searchPathRef;
x_20 = lean_io_ref_set(x_19, x_18, x_15);
return x_20;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_3);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_Lean_setSearchPathFromString(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l___private_init_lean_path_2__searchPathSep;
x_4 = l_String_split(x_1, x_3);
x_5 = l_Lean_setSearchPath(x_4, x_2);
return x_5;
}
}
obj* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_app_dir(x_1);
return x_2;
}
}
obj* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_app_dir(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::box(0);
lean::cnstr_set(x_2, 0, x_5);
x_6 = l_System_FilePath_dirName(x_4);
x_7 = lean_io_realpath(x_6, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_System_FilePath_dirName(x_8);
x_13 = lean_io_realpath(x_12, x_11);
return x_13;
}
}
else
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_2);
if (x_14 == 0)
{
return x_2;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = lean::cnstr_get(x_2, 0);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_2);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
}
}
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_getBuiltinSearchPath___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("..");
return x_1;
}
}
obj* _init_l_Lean_getBuiltinSearchPath___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("library");
return x_1;
}
}
obj* _init_l_Lean_getBuiltinSearchPath___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("lib");
return x_1;
}
}
obj* _init_l_Lean_getBuiltinSearchPath___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("lean");
return x_1;
}
}
obj* l_Lean_getBuiltinSearchPath(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::box(0);
lean::cnstr_set(x_2, 0, x_5);
x_6 = l___private_init_lean_path_1__pathSep;
x_7 = lean_string_append(x_4, x_6);
x_8 = l_Lean_getBuiltinSearchPath___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_6);
x_11 = l_Lean_getBuiltinSearchPath___closed__2;
lean::inc(x_10);
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_io_is_dir(x_12, x_2);
if (lean::obj_tag(x_13) == 0)
{
uint8 x_14; 
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; uint8 x_16; 
x_15 = lean::cnstr_get(x_13, 0);
lean::cnstr_set(x_13, 0, x_5);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_12);
x_17 = l_Lean_getBuiltinSearchPath___closed__3;
x_18 = lean_string_append(x_10, x_17);
x_19 = lean_string_append(x_18, x_6);
x_20 = l_Lean_getBuiltinSearchPath___closed__4;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_string_append(x_21, x_6);
x_23 = lean_string_append(x_22, x_11);
x_24 = lean_io_is_dir(x_23, x_13);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; uint8 x_26; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_26 = lean::unbox(x_25);
lean::dec(x_25);
if (x_26 == 0)
{
uint8 x_27; 
lean::dec(x_23);
x_27 = !lean::is_exclusive(x_24);
if (x_27 == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_24, 0);
lean::dec(x_28);
x_29 = lean::box(0);
lean::cnstr_set(x_24, 0, x_29);
return x_24;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_24, 1);
lean::inc(x_30);
lean::dec(x_24);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8 x_33; 
x_33 = !lean::is_exclusive(x_24);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_24, 0);
lean::dec(x_34);
lean::cnstr_set(x_24, 0, x_5);
x_35 = l_Lean_realPathNormalized(x_23, x_24);
if (lean::obj_tag(x_35) == 0)
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_35, 0);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
lean::cnstr_set(x_35, 0, x_39);
return x_35;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_35, 0);
x_41 = lean::cnstr_get(x_35, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_35);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set(x_43, 1, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
obj* x_46; obj* x_47; obj* x_48; 
x_46 = lean::cnstr_get(x_35, 0);
x_47 = lean::cnstr_get(x_35, 1);
lean::inc(x_47);
lean::inc(x_46);
lean::dec(x_35);
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
obj* x_49; obj* x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_24, 1);
lean::inc(x_49);
lean::dec(x_24);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_5);
lean::cnstr_set(x_50, 1, x_49);
x_51 = l_Lean_realPathNormalized(x_23, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_54 = x_51;
} else {
 lean::dec_ref(x_51);
 x_54 = lean::box(0);
}
x_55 = lean::box(0);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_52);
lean::cnstr_set(x_56, 1, x_55);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::cnstr_get(x_51, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_51, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_60 = x_51;
} else {
 lean::dec_ref(x_51);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
uint8 x_62; 
lean::dec(x_23);
x_62 = !lean::is_exclusive(x_24);
if (x_62 == 0)
{
return x_24;
}
else
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = lean::cnstr_get(x_24, 0);
x_64 = lean::cnstr_get(x_24, 1);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_24);
x_65 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
obj* x_66; 
lean::dec(x_10);
x_66 = l_Lean_realPathNormalized(x_12, x_13);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_66);
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_66, 0);
x_69 = lean::box(0);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_69);
lean::cnstr_set(x_66, 0, x_70);
return x_66;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_71 = lean::cnstr_get(x_66, 0);
x_72 = lean::cnstr_get(x_66, 1);
lean::inc(x_72);
lean::inc(x_71);
lean::dec(x_66);
x_73 = lean::box(0);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_72);
return x_75;
}
}
else
{
uint8 x_76; 
x_76 = !lean::is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_66, 0);
x_78 = lean::cnstr_get(x_66, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_66);
x_79 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; uint8 x_83; 
x_80 = lean::cnstr_get(x_13, 0);
x_81 = lean::cnstr_get(x_13, 1);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_13);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_5);
lean::cnstr_set(x_82, 1, x_81);
x_83 = lean::unbox(x_80);
lean::dec(x_80);
if (x_83 == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_12);
x_84 = l_Lean_getBuiltinSearchPath___closed__3;
x_85 = lean_string_append(x_10, x_84);
x_86 = lean_string_append(x_85, x_6);
x_87 = l_Lean_getBuiltinSearchPath___closed__4;
x_88 = lean_string_append(x_86, x_87);
x_89 = lean_string_append(x_88, x_6);
x_90 = lean_string_append(x_89, x_11);
x_91 = lean_io_is_dir(x_90, x_82);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; uint8 x_93; 
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_93 = lean::unbox(x_92);
lean::dec(x_92);
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_90);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_95 = x_91;
} else {
 lean::dec_ref(x_91);
 x_95 = lean::box(0);
}
x_96 = lean::box(0);
if (lean::is_scalar(x_95)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_95;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
return x_97;
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_98 = lean::cnstr_get(x_91, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_99 = x_91;
} else {
 lean::dec_ref(x_91);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_5);
lean::cnstr_set(x_100, 1, x_98);
x_101 = l_Lean_realPathNormalized(x_90, x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_101, 1);
lean::inc(x_103);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_104 = x_101;
} else {
 lean::dec_ref(x_101);
 x_104 = lean::box(0);
}
x_105 = lean::box(0);
x_106 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set(x_106, 1, x_105);
if (lean::is_scalar(x_104)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_104;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_103);
return x_107;
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_108 = lean::cnstr_get(x_101, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_101, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_101)) {
 lean::cnstr_release(x_101, 0);
 lean::cnstr_release(x_101, 1);
 x_110 = x_101;
} else {
 lean::dec_ref(x_101);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
lean::cnstr_set(x_111, 1, x_109);
return x_111;
}
}
}
else
{
obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_90);
x_112 = lean::cnstr_get(x_91, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get(x_91, 1);
lean::inc(x_113);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_114 = x_91;
} else {
 lean::dec_ref(x_91);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set(x_115, 1, x_113);
return x_115;
}
}
else
{
obj* x_116; 
lean::dec(x_10);
x_116 = l_Lean_realPathNormalized(x_12, x_82);
if (lean::obj_tag(x_116) == 0)
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_116, 1);
lean::inc(x_118);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 x_119 = x_116;
} else {
 lean::dec_ref(x_116);
 x_119 = lean::box(0);
}
x_120 = lean::box(0);
x_121 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set(x_121, 1, x_120);
if (lean::is_scalar(x_119)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_119;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_118);
return x_122;
}
else
{
obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_116, 1);
lean::inc(x_124);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 lean::cnstr_release(x_116, 1);
 x_125 = x_116;
} else {
 lean::dec_ref(x_116);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
lean::cnstr_set(x_126, 1, x_124);
return x_126;
}
}
}
}
else
{
uint8 x_127; 
lean::dec(x_12);
lean::dec(x_10);
x_127 = !lean::is_exclusive(x_13);
if (x_127 == 0)
{
return x_13;
}
else
{
obj* x_128; obj* x_129; obj* x_130; 
x_128 = lean::cnstr_get(x_13, 0);
x_129 = lean::cnstr_get(x_13, 1);
lean::inc(x_129);
lean::inc(x_128);
lean::dec(x_13);
x_130 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_130, 0, x_128);
lean::cnstr_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_131 = lean::cnstr_get(x_2, 0);
x_132 = lean::cnstr_get(x_2, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_2);
x_133 = lean::box(0);
x_134 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_132);
x_135 = l___private_init_lean_path_1__pathSep;
x_136 = lean_string_append(x_131, x_135);
x_137 = l_Lean_getBuiltinSearchPath___closed__1;
x_138 = lean_string_append(x_136, x_137);
x_139 = lean_string_append(x_138, x_135);
x_140 = l_Lean_getBuiltinSearchPath___closed__2;
lean::inc(x_139);
x_141 = lean_string_append(x_139, x_140);
x_142 = lean_io_is_dir(x_141, x_134);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; uint8 x_147; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::cnstr_get(x_142, 1);
lean::inc(x_144);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_145 = x_142;
} else {
 lean::dec_ref(x_142);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_133);
lean::cnstr_set(x_146, 1, x_144);
x_147 = lean::unbox(x_143);
lean::dec(x_143);
if (x_147 == 0)
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; 
lean::dec(x_141);
x_148 = l_Lean_getBuiltinSearchPath___closed__3;
x_149 = lean_string_append(x_139, x_148);
x_150 = lean_string_append(x_149, x_135);
x_151 = l_Lean_getBuiltinSearchPath___closed__4;
x_152 = lean_string_append(x_150, x_151);
x_153 = lean_string_append(x_152, x_135);
x_154 = lean_string_append(x_153, x_140);
x_155 = lean_io_is_dir(x_154, x_146);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; uint8 x_157; 
x_156 = lean::cnstr_get(x_155, 0);
lean::inc(x_156);
x_157 = lean::unbox(x_156);
lean::dec(x_156);
if (x_157 == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_154);
x_158 = lean::cnstr_get(x_155, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_159 = x_155;
} else {
 lean::dec_ref(x_155);
 x_159 = lean::box(0);
}
x_160 = lean::box(0);
if (lean::is_scalar(x_159)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_159;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_158);
return x_161;
}
else
{
obj* x_162; obj* x_163; obj* x_164; obj* x_165; 
x_162 = lean::cnstr_get(x_155, 1);
lean::inc(x_162);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_163 = x_155;
} else {
 lean::dec_ref(x_155);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_133);
lean::cnstr_set(x_164, 1, x_162);
x_165 = l_Lean_realPathNormalized(x_154, x_164);
if (lean::obj_tag(x_165) == 0)
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_165, 1);
lean::inc(x_167);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_168 = x_165;
} else {
 lean::dec_ref(x_165);
 x_168 = lean::box(0);
}
x_169 = lean::box(0);
x_170 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set(x_170, 1, x_169);
if (lean::is_scalar(x_168)) {
 x_171 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_171 = x_168;
}
lean::cnstr_set(x_171, 0, x_170);
lean::cnstr_set(x_171, 1, x_167);
return x_171;
}
else
{
obj* x_172; obj* x_173; obj* x_174; obj* x_175; 
x_172 = lean::cnstr_get(x_165, 0);
lean::inc(x_172);
x_173 = lean::cnstr_get(x_165, 1);
lean::inc(x_173);
if (lean::is_exclusive(x_165)) {
 lean::cnstr_release(x_165, 0);
 lean::cnstr_release(x_165, 1);
 x_174 = x_165;
} else {
 lean::dec_ref(x_165);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
lean::cnstr_set(x_175, 1, x_173);
return x_175;
}
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_154);
x_176 = lean::cnstr_get(x_155, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_155, 1);
lean::inc(x_177);
if (lean::is_exclusive(x_155)) {
 lean::cnstr_release(x_155, 0);
 lean::cnstr_release(x_155, 1);
 x_178 = x_155;
} else {
 lean::dec_ref(x_155);
 x_178 = lean::box(0);
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_176);
lean::cnstr_set(x_179, 1, x_177);
return x_179;
}
}
else
{
obj* x_180; 
lean::dec(x_139);
x_180 = l_Lean_realPathNormalized(x_141, x_146);
if (lean::obj_tag(x_180) == 0)
{
obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_182 = lean::cnstr_get(x_180, 1);
lean::inc(x_182);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_183 = x_180;
} else {
 lean::dec_ref(x_180);
 x_183 = lean::box(0);
}
x_184 = lean::box(0);
x_185 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_185, 0, x_181);
lean::cnstr_set(x_185, 1, x_184);
if (lean::is_scalar(x_183)) {
 x_186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_186 = x_183;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_182);
return x_186;
}
else
{
obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_187 = lean::cnstr_get(x_180, 0);
lean::inc(x_187);
x_188 = lean::cnstr_get(x_180, 1);
lean::inc(x_188);
if (lean::is_exclusive(x_180)) {
 lean::cnstr_release(x_180, 0);
 lean::cnstr_release(x_180, 1);
 x_189 = x_180;
} else {
 lean::dec_ref(x_180);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
lean::cnstr_set(x_190, 1, x_188);
return x_190;
}
}
}
else
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_141);
lean::dec(x_139);
x_191 = lean::cnstr_get(x_142, 0);
lean::inc(x_191);
x_192 = lean::cnstr_get(x_142, 1);
lean::inc(x_192);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_193 = x_142;
} else {
 lean::dec_ref(x_142);
 x_193 = lean::box(0);
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_191);
lean::cnstr_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
uint8 x_195; 
x_195 = !lean::is_exclusive(x_2);
if (x_195 == 0)
{
return x_2;
}
else
{
obj* x_196; obj* x_197; obj* x_198; 
x_196 = lean::cnstr_get(x_2, 0);
x_197 = lean::cnstr_get(x_2, 1);
lean::inc(x_197);
lean::inc(x_196);
lean::dec(x_2);
x_198 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_198, 0, x_196);
lean::cnstr_set(x_198, 1, x_197);
return x_198;
}
}
}
}
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_getenv(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_getSearchPathFromEnv___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("LEAN_PATH");
return x_1;
}
}
obj* _init_l_Lean_getSearchPathFromEnv___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_Lean_getSearchPathFromEnv(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_getSearchPathFromEnv___closed__1;
x_3 = lean_io_getenv(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
lean::dec(x_6);
x_7 = l_Lean_getSearchPathFromEnv___closed__2;
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_9 = l_Lean_getSearchPathFromEnv___closed__2;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_3);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_3, 0);
lean::dec(x_12);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_14 = l___private_init_lean_path_2__searchPathSep;
x_15 = l_String_split(x_13, x_14);
lean::cnstr_set(x_3, 0, x_15);
return x_3;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_18 = l___private_init_lean_path_2__searchPathSep;
x_19 = l_String_split(x_17, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_16);
return x_20;
}
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_3);
if (x_21 == 0)
{
return x_3;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_3, 0);
x_23 = lean::cnstr_get(x_3, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_3);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* lean_init_search_path(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = l_Lean_getSearchPathFromEnv(x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_Lean_getBuiltinSearchPath(x_3);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_7, 0);
lean::cnstr_set(x_7, 0, x_6);
x_10 = l_List_append___rarg(x_5, x_9);
x_11 = l_Lean_setSearchPath(x_10, x_7);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_7, 0);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_7);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = l_List_append___rarg(x_5, x_12);
x_16 = l_Lean_setSearchPath(x_15, x_14);
return x_16;
}
}
else
{
uint8 x_17; 
lean::dec(x_5);
x_17 = !lean::is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_7, 0);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_7);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_3, 0);
x_22 = lean::cnstr_get(x_3, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_3);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
x_25 = l_Lean_getBuiltinSearchPath(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_28 = x_25;
} else {
 lean::dec_ref(x_25);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_23);
lean::cnstr_set(x_29, 1, x_27);
x_30 = l_List_append___rarg(x_21, x_26);
x_31 = l_Lean_setSearchPath(x_30, x_29);
return x_31;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_21);
x_32 = lean::cnstr_get(x_25, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_25, 1);
lean::inc(x_33);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_34 = x_25;
} else {
 lean::dec_ref(x_25);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8 x_36; 
x_36 = !lean::is_exclusive(x_3);
if (x_36 == 0)
{
return x_3;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_3, 0);
x_38 = lean::cnstr_get(x_3, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_3);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
obj* x_40; obj* x_41; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
x_41 = l_Lean_setSearchPathFromString(x_40, x_2);
return x_41;
}
}
}
obj* l_IO_fileExists___at_Lean_findFile___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_file_exists(x_1, x_2);
return x_3;
}
}
obj* _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_extSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
obj* _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("default");
return x_1;
}
}
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_15; uint8 x_16; 
x_15 = lean_array_get_size(x_3);
x_16 = lean_nat_dec_lt(x_4, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
uint8 x_17; 
lean::dec(x_4);
x_17 = !lean::is_exclusive(x_5);
if (x_17 == 0)
{
obj* x_18; obj* x_19; 
x_18 = lean::cnstr_get(x_5, 0);
lean::dec(x_18);
x_19 = lean::box(0);
lean::cnstr_set(x_5, 0, x_19);
return x_5;
}
else
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = lean::cnstr_get(x_5, 1);
lean::inc(x_20);
lean::dec(x_5);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
return x_22;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_23 = lean_array_fget(x_3, x_4);
x_24 = l___private_init_lean_path_1__pathSep;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_2);
x_49 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
lean::inc(x_26);
x_50 = lean_string_append(x_26, x_49);
x_51 = lean_string_append(x_50, x_1);
x_52 = lean_io_file_exists(x_51, x_5);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; uint8 x_54; 
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_54 = lean::unbox(x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_51);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_56 = lean::box(0);
x_27 = x_56;
x_28 = x_55;
goto block_48;
}
else
{
obj* x_57; obj* x_58; 
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
lean::dec(x_52);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_51);
x_27 = x_58;
x_28 = x_57;
goto block_48;
}
}
else
{
uint8 x_59; 
lean::dec(x_51);
lean::dec(x_26);
lean::dec(x_4);
x_59 = !lean::is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::cnstr_get(x_52, 0);
x_61 = lean::cnstr_get(x_52, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_52);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_61);
return x_62;
}
}
block_48:
{
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_28);
x_31 = lean_string_append(x_26, x_24);
x_32 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_string_append(x_35, x_1);
x_37 = lean_io_file_exists(x_36, x_30);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; uint8 x_39; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_39 = lean::unbox(x_38);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; 
lean::dec(x_36);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_41 = lean::box(0);
x_6 = x_41;
x_7 = x_40;
goto block_14;
}
else
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_36);
x_6 = x_43;
x_7 = x_42;
goto block_14;
}
}
else
{
uint8 x_44; 
lean::dec(x_36);
lean::dec(x_4);
x_44 = !lean::is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
obj* x_45; obj* x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get(x_37, 1);
lean::inc(x_46);
lean::inc(x_45);
lean::dec(x_37);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean::dec(x_26);
x_6 = x_27;
x_7 = x_28;
goto block_14;
}
}
}
block_14:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean_nat_add(x_4, x_10);
lean::dec(x_4);
x_4 = x_11;
x_5 = x_9;
goto _start;
}
else
{
obj* x_13; 
lean::dec(x_4);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_6);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
}
}
obj* l_Lean_findFile(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_System_FilePath_normalizePath(x_1);
x_5 = l_Lean_searchPathRef;
x_6 = lean_io_ref_get(x_5, x_3);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::box(0);
lean::cnstr_set(x_6, 0, x_9);
x_10 = lean::mk_nat_obj(0u);
x_11 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_2, x_4, x_8, x_10, x_6);
lean::dec(x_8);
lean::dec(x_4);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::mk_nat_obj(0u);
x_17 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_2, x_4, x_12, x_16, x_15);
lean::dec(x_12);
lean::dec(x_4);
return x_17;
}
}
else
{
uint8 x_18; 
lean::dec(x_4);
x_18 = !lean::is_exclusive(x_6);
if (x_18 == 0)
{
return x_6;
}
else
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_6, 0);
x_20 = lean::cnstr_get(x_6, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_6);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
}
obj* l_IO_fileExists___at_Lean_findFile___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_IO_fileExists___at_Lean_findFile___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_findFile___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_findFile(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_modNameToFileName___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = l_String_splitAux___main___closed__1;
return x_2;
}
case 1:
{
obj* x_3; obj* x_4; obj* x_5; uint8 x_6; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean_name_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = l_Lean_modNameToFileName___main(x_3);
x_8 = l___private_init_lean_path_1__pathSep;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_string_append(x_9, x_4);
return x_10;
}
else
{
lean::inc(x_4);
return x_4;
}
}
default: 
{
obj* x_11; 
x_11 = lean::cnstr_get(x_1, 0);
x_1 = x_11;
goto _start;
}
}
}
}
obj* l_Lean_modNameToFileName___main___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_modNameToFileName___main(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_modNameToFileName(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_modNameToFileName___main(x_1);
return x_2;
}
}
obj* l_Lean_modNameToFileName___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_modNameToFileName(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_addRel___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Lean_addRel___main(x_1, x_6);
lean::dec(x_6);
x_8 = l___private_init_lean_path_1__pathSep;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_getBuiltinSearchPath___closed__1;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Lean_addRel___main___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_addRel___main(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_addRel(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_addRel___main(x_1, x_2);
return x_3;
}
}
obj* l_Lean_addRel___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_addRel(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_findLeanFile___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("module '");
return x_1;
}
}
obj* _init_l_Lean_findLeanFile___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' not found");
return x_1;
}
}
obj* l_Lean_findLeanFile(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_modNameToFileName___main(x_1);
x_5 = l_Lean_findFile(x_4, x_2, x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = l_Lean_findLeanFile___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean::dec(x_10);
x_13 = l_Lean_findLeanFile___closed__2;
x_14 = lean_string_append(x_12, x_13);
lean::cnstr_set_tag(x_5, 1);
lean::cnstr_set(x_5, 0, x_14);
return x_5;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::dec(x_5);
x_16 = l_Lean_Name_toString___closed__1;
x_17 = l_Lean_Name_toStringWithSep___main(x_16, x_1);
x_18 = l_Lean_findLeanFile___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean::dec(x_17);
x_20 = l_Lean_findLeanFile___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_15);
return x_22;
}
}
else
{
uint8 x_23; 
lean::dec(x_1);
x_23 = !lean::is_exclusive(x_5);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_5, 0);
lean::dec(x_24);
x_25 = lean::cnstr_get(x_6, 0);
lean::inc(x_25);
lean::dec(x_6);
x_26 = lean::box(0);
lean::cnstr_set(x_5, 0, x_26);
x_27 = l_Lean_realPathNormalized(x_25, x_5);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_5, 1);
lean::inc(x_28);
lean::dec(x_5);
x_29 = lean::cnstr_get(x_6, 0);
lean::inc(x_29);
lean::dec(x_6);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
x_32 = l_Lean_realPathNormalized(x_29, x_31);
return x_32;
}
}
}
else
{
uint8 x_33; 
lean::dec(x_1);
x_33 = !lean::is_exclusive(x_5);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_5, 0);
x_35 = lean::cnstr_get(x_5, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_5);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
}
obj* l_Lean_findLeanFile___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_findLeanFile(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* _init_l_Lean_findOLean___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("olean");
return x_1;
}
}
obj* l_Lean_findOLean(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_findOLean___closed__1;
x_4 = l_Lean_findLeanFile(x_1, x_3, x_2);
return x_4;
}
}
obj* lean_find_lean(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_getBuiltinSearchPath___closed__4;
x_4 = l_Lean_findLeanFile(x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_6; 
lean::dec(x_3);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; uint8 x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_String_isPrefixOf(x_7, x_1);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_7);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean_nat_add(x_3, x_9);
lean::dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
obj* x_12; 
lean::dec(x_3);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_7);
return x_12;
}
}
}
}
obj* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(uint8 x_1, obj* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_6 = l_String_quote(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean::dec(x_6);
x_9 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_1, x_5);
x_10 = lean_string_append(x_8, x_9);
lean::dec(x_9);
return x_10;
}
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_11; 
x_11 = l_String_splitAux___main___closed__1;
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_14 = l_String_quote(x_12);
x_15 = 0;
x_16 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_15, x_13);
x_17 = lean_string_append(x_14, x_16);
lean::dec(x_16);
return x_17;
}
}
}
}
obj* l_List_repr___at_Lean_findAtSearchPath___spec__2(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = 1;
x_4 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean::dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
obj* _init_l_Lean_findAtSearchPath___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("file '");
return x_1;
}
}
obj* _init_l_Lean_findAtSearchPath___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' not in the search path ");
return x_1;
}
}
obj* l_Lean_findAtSearchPath(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_realPathNormalized(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_Lean_searchPathRef;
x_8 = lean_io_ref_get(x_7, x_3);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_5, x_10, x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_13 = l_Lean_findAtSearchPath___closed__1;
x_14 = lean_string_append(x_13, x_5);
lean::dec(x_5);
x_15 = l_Lean_findAtSearchPath___closed__2;
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Array_toList___rarg(x_10);
lean::dec(x_10);
x_18 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_17);
x_19 = lean_string_append(x_16, x_18);
lean::dec(x_18);
lean::cnstr_set_tag(x_8, 1);
lean::cnstr_set(x_8, 0, x_19);
return x_8;
}
else
{
obj* x_20; 
lean::dec(x_10);
lean::dec(x_5);
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
lean::cnstr_set(x_8, 0, x_20);
return x_8;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_8, 0);
x_22 = lean::cnstr_get(x_8, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_8);
x_23 = lean::mk_nat_obj(0u);
x_24 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_5, x_21, x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = l_Lean_findAtSearchPath___closed__1;
x_26 = lean_string_append(x_25, x_5);
lean::dec(x_5);
x_27 = l_Lean_findAtSearchPath___closed__2;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_Array_toList___rarg(x_21);
lean::dec(x_21);
x_30 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_29);
x_31 = lean_string_append(x_28, x_30);
lean::dec(x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_22);
return x_32;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_21);
lean::dec(x_5);
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
lean::dec(x_24);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_22);
return x_34;
}
}
}
else
{
uint8 x_35; 
lean::dec(x_5);
x_35 = !lean::is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_8, 0);
x_37 = lean::cnstr_get(x_8, 1);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_8);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_3, 0);
x_40 = lean::cnstr_get(x_3, 1);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_3);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_40);
x_43 = l_Lean_searchPathRef;
x_44 = lean_io_ref_get(x_43, x_42);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_47 = x_44;
} else {
 lean::dec_ref(x_44);
 x_47 = lean::box(0);
}
x_48 = lean::mk_nat_obj(0u);
x_49 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_39, x_45, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = l_Lean_findAtSearchPath___closed__1;
x_51 = lean_string_append(x_50, x_39);
lean::dec(x_39);
x_52 = l_Lean_findAtSearchPath___closed__2;
x_53 = lean_string_append(x_51, x_52);
x_54 = l_Array_toList___rarg(x_45);
lean::dec(x_45);
x_55 = l_List_repr___at_Lean_findAtSearchPath___spec__2(x_54);
x_56 = lean_string_append(x_53, x_55);
lean::dec(x_55);
if (lean::is_scalar(x_47)) {
 x_57 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_57 = x_47;
 lean::cnstr_set_tag(x_57, 1);
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_46);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_45);
lean::dec(x_39);
x_58 = lean::cnstr_get(x_49, 0);
lean::inc(x_58);
lean::dec(x_49);
if (lean::is_scalar(x_47)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_47;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_46);
return x_59;
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_39);
x_60 = lean::cnstr_get(x_44, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_44, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 x_62 = x_44;
} else {
 lean::dec_ref(x_44);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
uint8 x_64; 
x_64 = !lean::is_exclusive(x_3);
if (x_64 == 0)
{
return x_3;
}
else
{
obj* x_65; obj* x_66; obj* x_67; 
x_65 = lean::cnstr_get(x_3, 0);
x_66 = lean::cnstr_get(x_3, 1);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_3);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
}
}
}
obj* l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mfindAux___main___at_Lean_findAtSearchPath___spec__1(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3___boxed(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
lean::dec(x_1);
x_4 = l_List_reprAux___main___at_Lean_findAtSearchPath___spec__3(x_3, x_2);
return x_4;
}
}
obj* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
return x_1;
}
else
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_2, 1);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean_name_mk_string(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
obj* _init_l_Lean_moduleNameOfFileName___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to convert file '");
return x_1;
}
}
obj* _init_l_Lean_moduleNameOfFileName___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' to module name, path is not a prefix of the given file");
return x_1;
}
}
obj* _init_l_Lean_moduleNameOfFileName___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' to module name, extension is missing");
return x_1;
}
}
obj* _init_l_Lean_moduleNameOfFileName___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' to module name, module name '");
return x_1;
}
}
obj* _init_l_Lean_moduleNameOfFileName___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' resolves to '");
return x_1;
}
}
obj* lean_module_name_of_file(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
lean::inc(x_1);
x_3 = l_Lean_findAtSearchPath(x_1, x_2);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
x_7 = l_Lean_realPathNormalized(x_1, x_3);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint32 x_14; uint32 x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_10 = x_7;
} else {
 lean::dec_ref(x_7);
 x_10 = lean::box(0);
}
x_11 = lean_string_length(x_5);
x_12 = l_String_drop(x_8, x_11);
lean::dec(x_11);
x_13 = lean::mk_nat_obj(0u);
x_14 = lean_string_utf8_get(x_12, x_13);
x_15 = l_System_FilePath_pathSeparator;
x_16 = x_14 == x_15;
x_17 = l___private_init_lean_path_1__pathSep;
x_18 = lean_string_append(x_5, x_17);
if (x_16 == 0)
{
x_19 = x_12;
goto block_81;
}
else
{
obj* x_82; obj* x_83; 
x_82 = lean::mk_nat_obj(1u);
x_83 = l_String_drop(x_12, x_82);
lean::dec(x_12);
x_19 = x_83;
goto block_81;
}
block_81:
{
obj* x_20; uint8 x_21; 
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_dec_eq(x_20, x_8);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_19);
x_22 = l_Lean_moduleNameOfFileName___closed__1;
x_23 = lean_string_append(x_22, x_8);
lean::dec(x_8);
x_24 = l_Lean_moduleNameOfFileName___closed__2;
x_25 = lean_string_append(x_23, x_24);
if (lean::is_scalar(x_10)) {
 x_26 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_26 = x_10;
 lean::cnstr_set_tag(x_26, 1);
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
return x_26;
}
else
{
uint32 x_27; obj* x_28; 
x_27 = 46;
x_28 = l_String_revPosOf(x_19, x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_19);
x_29 = l_Lean_moduleNameOfFileName___closed__1;
x_30 = lean_string_append(x_29, x_8);
lean::dec(x_8);
x_31 = l_Lean_moduleNameOfFileName___closed__3;
x_32 = lean_string_append(x_30, x_31);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_33 = x_10;
 lean::cnstr_set_tag(x_33, 1);
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_34 = lean::cnstr_get(x_28, 0);
lean::inc(x_34);
lean::dec(x_28);
if (lean::is_scalar(x_10)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_10;
}
lean::cnstr_set(x_35, 0, x_6);
lean::cnstr_set(x_35, 1, x_9);
x_36 = lean_string_utf8_extract(x_19, x_13, x_34);
x_37 = lean::mk_nat_obj(1u);
x_38 = lean_nat_add(x_34, x_37);
lean::dec(x_34);
x_39 = lean_string_utf8_byte_size(x_19);
x_40 = lean_string_utf8_extract(x_19, x_38, x_39);
lean::dec(x_39);
lean::dec(x_38);
lean::dec(x_19);
x_41 = l_String_split(x_36, x_17);
x_42 = lean::box(0);
x_43 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_42, x_41);
lean::inc(x_43);
x_44 = l_Lean_findLeanFile(x_43, x_40, x_35);
lean::dec(x_40);
if (lean::obj_tag(x_44) == 0)
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_44);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::cnstr_get(x_44, 0);
x_47 = lean_string_dec_eq(x_8, x_46);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_48 = l_Lean_moduleNameOfFileName___closed__1;
x_49 = lean_string_append(x_48, x_8);
lean::dec(x_8);
x_50 = l_Lean_moduleNameOfFileName___closed__4;
x_51 = lean_string_append(x_49, x_50);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_43);
x_54 = lean_string_append(x_51, x_53);
lean::dec(x_53);
x_55 = l_Lean_moduleNameOfFileName___closed__5;
x_56 = lean_string_append(x_54, x_55);
x_57 = lean_string_append(x_56, x_46);
lean::dec(x_46);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean_string_append(x_57, x_58);
lean::cnstr_set_tag(x_44, 1);
lean::cnstr_set(x_44, 0, x_59);
return x_44;
}
else
{
lean::dec(x_46);
lean::dec(x_8);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
}
else
{
obj* x_60; obj* x_61; uint8 x_62; 
x_60 = lean::cnstr_get(x_44, 0);
x_61 = lean::cnstr_get(x_44, 1);
lean::inc(x_61);
lean::inc(x_60);
lean::dec(x_44);
x_62 = lean_string_dec_eq(x_8, x_60);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_63 = l_Lean_moduleNameOfFileName___closed__1;
x_64 = lean_string_append(x_63, x_8);
lean::dec(x_8);
x_65 = l_Lean_moduleNameOfFileName___closed__4;
x_66 = lean_string_append(x_64, x_65);
x_67 = l_Lean_Name_toString___closed__1;
x_68 = l_Lean_Name_toStringWithSep___main(x_67, x_43);
x_69 = lean_string_append(x_66, x_68);
lean::dec(x_68);
x_70 = l_Lean_moduleNameOfFileName___closed__5;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_string_append(x_71, x_60);
lean::dec(x_60);
x_73 = l_Char_HasRepr___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
else
{
obj* x_76; 
lean::dec(x_60);
lean::dec(x_8);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_43);
lean::cnstr_set(x_76, 1, x_61);
return x_76;
}
}
}
else
{
uint8 x_77; 
lean::dec(x_43);
lean::dec(x_8);
x_77 = !lean::is_exclusive(x_44);
if (x_77 == 0)
{
return x_44;
}
else
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::cnstr_get(x_44, 0);
x_79 = lean::cnstr_get(x_44, 1);
lean::inc(x_79);
lean::inc(x_78);
lean::dec(x_44);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
else
{
uint8 x_84; 
lean::dec(x_5);
x_84 = !lean::is_exclusive(x_7);
if (x_84 == 0)
{
return x_7;
}
else
{
obj* x_85; obj* x_86; obj* x_87; 
x_85 = lean::cnstr_get(x_7, 0);
x_86 = lean::cnstr_get(x_7, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_7);
x_87 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_88 = lean::cnstr_get(x_3, 0);
x_89 = lean::cnstr_get(x_3, 1);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_3);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_89);
x_92 = l_Lean_realPathNormalized(x_1, x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; uint32 x_99; uint32 x_100; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; 
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_92, 1);
lean::inc(x_94);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_95 = x_92;
} else {
 lean::dec_ref(x_92);
 x_95 = lean::box(0);
}
x_96 = lean_string_length(x_88);
x_97 = l_String_drop(x_93, x_96);
lean::dec(x_96);
x_98 = lean::mk_nat_obj(0u);
x_99 = lean_string_utf8_get(x_97, x_98);
x_100 = l_System_FilePath_pathSeparator;
x_101 = x_99 == x_100;
x_102 = l___private_init_lean_path_1__pathSep;
x_103 = lean_string_append(x_88, x_102);
if (x_101 == 0)
{
x_104 = x_97;
goto block_152;
}
else
{
obj* x_153; obj* x_154; 
x_153 = lean::mk_nat_obj(1u);
x_154 = l_String_drop(x_97, x_153);
lean::dec(x_97);
x_104 = x_154;
goto block_152;
}
block_152:
{
obj* x_105; uint8 x_106; 
x_105 = lean_string_append(x_103, x_104);
x_106 = lean_string_dec_eq(x_105, x_93);
lean::dec(x_105);
if (x_106 == 0)
{
obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_104);
x_107 = l_Lean_moduleNameOfFileName___closed__1;
x_108 = lean_string_append(x_107, x_93);
lean::dec(x_93);
x_109 = l_Lean_moduleNameOfFileName___closed__2;
x_110 = lean_string_append(x_108, x_109);
if (lean::is_scalar(x_95)) {
 x_111 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_111 = x_95;
 lean::cnstr_set_tag(x_111, 1);
}
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_94);
return x_111;
}
else
{
uint32 x_112; obj* x_113; 
x_112 = 46;
x_113 = l_String_revPosOf(x_104, x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_104);
x_114 = l_Lean_moduleNameOfFileName___closed__1;
x_115 = lean_string_append(x_114, x_93);
lean::dec(x_93);
x_116 = l_Lean_moduleNameOfFileName___closed__3;
x_117 = lean_string_append(x_115, x_116);
if (lean::is_scalar(x_95)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_95;
 lean::cnstr_set_tag(x_118, 1);
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_94);
return x_118;
}
else
{
obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_119 = lean::cnstr_get(x_113, 0);
lean::inc(x_119);
lean::dec(x_113);
if (lean::is_scalar(x_95)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_95;
}
lean::cnstr_set(x_120, 0, x_90);
lean::cnstr_set(x_120, 1, x_94);
x_121 = lean_string_utf8_extract(x_104, x_98, x_119);
x_122 = lean::mk_nat_obj(1u);
x_123 = lean_nat_add(x_119, x_122);
lean::dec(x_119);
x_124 = lean_string_utf8_byte_size(x_104);
x_125 = lean_string_utf8_extract(x_104, x_123, x_124);
lean::dec(x_124);
lean::dec(x_123);
lean::dec(x_104);
x_126 = l_String_split(x_121, x_102);
x_127 = lean::box(0);
x_128 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_127, x_126);
lean::inc(x_128);
x_129 = l_Lean_findLeanFile(x_128, x_125, x_120);
lean::dec(x_125);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_131; obj* x_132; uint8 x_133; 
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_131 = lean::cnstr_get(x_129, 1);
lean::inc(x_131);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_132 = x_129;
} else {
 lean::dec_ref(x_129);
 x_132 = lean::box(0);
}
x_133 = lean_string_dec_eq(x_93, x_130);
if (x_133 == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; 
x_134 = l_Lean_moduleNameOfFileName___closed__1;
x_135 = lean_string_append(x_134, x_93);
lean::dec(x_93);
x_136 = l_Lean_moduleNameOfFileName___closed__4;
x_137 = lean_string_append(x_135, x_136);
x_138 = l_Lean_Name_toString___closed__1;
x_139 = l_Lean_Name_toStringWithSep___main(x_138, x_128);
x_140 = lean_string_append(x_137, x_139);
lean::dec(x_139);
x_141 = l_Lean_moduleNameOfFileName___closed__5;
x_142 = lean_string_append(x_140, x_141);
x_143 = lean_string_append(x_142, x_130);
lean::dec(x_130);
x_144 = l_Char_HasRepr___closed__1;
x_145 = lean_string_append(x_143, x_144);
if (lean::is_scalar(x_132)) {
 x_146 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_146 = x_132;
 lean::cnstr_set_tag(x_146, 1);
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_131);
return x_146;
}
else
{
obj* x_147; 
lean::dec(x_130);
lean::dec(x_93);
if (lean::is_scalar(x_132)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_132;
}
lean::cnstr_set(x_147, 0, x_128);
lean::cnstr_set(x_147, 1, x_131);
return x_147;
}
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_128);
lean::dec(x_93);
x_148 = lean::cnstr_get(x_129, 0);
lean::inc(x_148);
x_149 = lean::cnstr_get(x_129, 1);
lean::inc(x_149);
if (lean::is_exclusive(x_129)) {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 x_150 = x_129;
} else {
 lean::dec_ref(x_129);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
lean::cnstr_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_88);
x_155 = lean::cnstr_get(x_92, 0);
lean::inc(x_155);
x_156 = lean::cnstr_get(x_92, 1);
lean::inc(x_156);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_157 = x_92;
} else {
 lean::dec_ref(x_92);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
lean::cnstr_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
uint8 x_159; 
lean::dec(x_1);
x_159 = !lean::is_exclusive(x_3);
if (x_159 == 0)
{
return x_3;
}
else
{
obj* x_160; obj* x_161; obj* x_162; 
x_160 = lean::cnstr_get(x_3, 0);
x_161 = lean::cnstr_get(x_3, 1);
lean::inc(x_161);
lean::inc(x_160);
lean::dec(x_3);
x_162 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_161);
return x_162;
}
}
}
}
obj* initialize_init_system_io(obj*);
obj* initialize_init_system_filepath(obj*);
obj* initialize_init_data_array_default(obj*);
obj* initialize_init_control_combinators(obj*);
obj* initialize_init_lean_name(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_path(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_system_io(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_system_filepath(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (lean::io_result_is_error(w)) return w;
l___private_init_lean_path_1__pathSep___closed__1 = _init_l___private_init_lean_path_1__pathSep___closed__1();
lean::mark_persistent(l___private_init_lean_path_1__pathSep___closed__1);
l___private_init_lean_path_1__pathSep = _init_l___private_init_lean_path_1__pathSep();
lean::mark_persistent(l___private_init_lean_path_1__pathSep);
l___private_init_lean_path_2__searchPathSep___closed__1 = _init_l___private_init_lean_path_2__searchPathSep___closed__1();
lean::mark_persistent(l___private_init_lean_path_2__searchPathSep___closed__1);
l___private_init_lean_path_2__searchPathSep = _init_l___private_init_lean_path_2__searchPathSep();
lean::mark_persistent(l___private_init_lean_path_2__searchPathSep);
w = l_Lean_mkSearchPathRef(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_searchPathRef = lean::io_result_get_value(w);
lean::mark_persistent(l_Lean_searchPathRef);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__1);
l_Lean_getBuiltinSearchPath___closed__2 = _init_l_Lean_getBuiltinSearchPath___closed__2();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__2);
l_Lean_getBuiltinSearchPath___closed__3 = _init_l_Lean_getBuiltinSearchPath___closed__3();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__3);
l_Lean_getBuiltinSearchPath___closed__4 = _init_l_Lean_getBuiltinSearchPath___closed__4();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__4);
l_Lean_getSearchPathFromEnv___closed__1 = _init_l_Lean_getSearchPathFromEnv___closed__1();
lean::mark_persistent(l_Lean_getSearchPathFromEnv___closed__1);
l_Lean_getSearchPathFromEnv___closed__2 = _init_l_Lean_getSearchPathFromEnv___closed__2();
lean::mark_persistent(l_Lean_getSearchPathFromEnv___closed__2);
l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1 = _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1();
lean::mark_persistent(l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__1);
l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2 = _init_l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2();
lean::mark_persistent(l_Array_mfindAux___main___at_Lean_findFile___spec__2___closed__2);
l_Lean_findLeanFile___closed__1 = _init_l_Lean_findLeanFile___closed__1();
lean::mark_persistent(l_Lean_findLeanFile___closed__1);
l_Lean_findLeanFile___closed__2 = _init_l_Lean_findLeanFile___closed__2();
lean::mark_persistent(l_Lean_findLeanFile___closed__2);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean::mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findAtSearchPath___closed__1 = _init_l_Lean_findAtSearchPath___closed__1();
lean::mark_persistent(l_Lean_findAtSearchPath___closed__1);
l_Lean_findAtSearchPath___closed__2 = _init_l_Lean_findAtSearchPath___closed__2();
lean::mark_persistent(l_Lean_findAtSearchPath___closed__2);
l_Lean_moduleNameOfFileName___closed__1 = _init_l_Lean_moduleNameOfFileName___closed__1();
lean::mark_persistent(l_Lean_moduleNameOfFileName___closed__1);
l_Lean_moduleNameOfFileName___closed__2 = _init_l_Lean_moduleNameOfFileName___closed__2();
lean::mark_persistent(l_Lean_moduleNameOfFileName___closed__2);
l_Lean_moduleNameOfFileName___closed__3 = _init_l_Lean_moduleNameOfFileName___closed__3();
lean::mark_persistent(l_Lean_moduleNameOfFileName___closed__3);
l_Lean_moduleNameOfFileName___closed__4 = _init_l_Lean_moduleNameOfFileName___closed__4();
lean::mark_persistent(l_Lean_moduleNameOfFileName___closed__4);
l_Lean_moduleNameOfFileName___closed__5 = _init_l_Lean_moduleNameOfFileName___closed__5();
lean::mark_persistent(l_Lean_moduleNameOfFileName___closed__5);
return w;
}
