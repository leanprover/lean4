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
obj* l_Lean_findLeanFile___closed__3;
obj* l_Lean_getBuiltinSearchPath___closed__2;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_List_mmap___main___at_Lean_setSearchPath___spec__1(obj*, obj*);
obj* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(obj*);
extern "C" obj* lean_io_realpath(obj*, obj*);
obj* l_IO_fileExists___at_Lean_findFile___spec__1(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(obj*, obj*);
obj* l_Lean_getSearchPathFromEnv___closed__1;
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Lean_findOLean(obj*, obj*);
obj* l_Lean_setSearchPath(obj*, obj*);
obj* l_Lean_modNameToFileName(obj*);
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
obj* l_IO_Prim_Ref_set(obj*, obj*, obj*, obj*);
obj* l_Lean_setSearchPathFromString(obj*, obj*);
obj* l_Array_mkEmpty(obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_findLeanFile___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_getBuiltinSearchPath___closed__5;
extern "C" obj* lean_io_getenv(obj*, obj*);
extern uint32 l_System_FilePath_searchPathSeparator;
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_findFile(obj*, obj*);
extern "C" obj* lean_io_file_exists(obj*, obj*);
obj* l_Lean_modNameToFileName___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_System_FilePath_dirName(obj*);
obj* l_Lean_getBuiltinSearchPath___closed__1;
obj* l_Array_fget(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_findLeanFile___closed__2;
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1___boxed(obj*, obj*);
obj* l_Lean_findLeanFile(obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_searchPathRef;
obj* l_IO_getEnv___at_Lean_getSearchPathFromEnv___spec__1(obj*, obj*);
obj* l_Lean_modNameToFileName___main(obj*);
obj* l_Lean_findLean___boxed(obj*, obj*, obj*);
obj* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(obj*, obj*);
obj* l___private_init_lean_path_1__pathSep___closed__1;
obj* l_IO_fileExists___at_Lean_findFile___spec__1___boxed(obj*, obj*);
obj* l_IO_Prim_mkRef(obj*, obj*, obj*);
obj* l_Lean_addRel___main___boxed(obj*, obj*);
obj* l_Lean_modNameToFileName___main___boxed(obj*);
obj* l_String_split(obj*, obj*);
obj* l_IO_Prim_Ref_get(obj*, obj*, obj*);
obj* l___private_init_lean_path_2__searchPathSep___closed__1;
obj* l_Array_size(obj*, obj*);
extern uint32 l_System_FilePath_extSeparator;
obj* l___private_init_lean_path_1__pathSep;
obj* l_Lean_findFile___boxed(obj*, obj*);
obj* l_Lean_getSearchPathFromEnv(obj*);
namespace lean {
obj* init_search_path_core(obj*, obj*);
}
extern uint32 l_System_FilePath_pathSeparator;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_findLeanFile___closed__1;
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_findLean(obj*, obj*, obj*);
obj* l_Lean_addRel(obj*, obj*);
obj* l_Lean_mkSearchPathRef(obj*);
obj* l_Lean_getBuiltinSearchPath___closed__3;
obj* l_Lean_getBuiltinSearchPath(obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_IO_realPath___at_Lean_mkSearchPathRef___spec__1(obj*, obj*);
obj* _init_l___private_init_lean_path_1__pathSep___closed__1() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean::string_push(x_1, x_2);
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
x_3 = lean::string_push(x_1, x_2);
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
obj* l_IO_realPath___at_Lean_mkSearchPathRef___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean_io_realpath(x_1, x_2);
return x_3;
}
}
obj* l_Lean_mkSearchPathRef(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_io_realpath(x_2, x_1);
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
x_8 = lean::mk_array(x_7, x_5);
x_9 = lean::io_mk_ref(x_8, x_3);
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
x_15 = lean::mk_array(x_14, x_10);
x_16 = lean::io_mk_ref(x_15, x_13);
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
x_12 = lean_io_realpath(x_10, x_2);
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
x_45 = lean_io_realpath(x_43, x_2);
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
x_8 = lean::mk_empty_array(x_7);
lean::dec(x_7);
x_9 = l_List_toArrayAux___main___rarg(x_5, x_8);
x_10 = l_Lean_searchPathRef;
x_11 = lean::io_ref_set(x_10, x_9, x_3);
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
x_17 = lean::mk_empty_array(x_16);
lean::dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_12, x_17);
x_19 = l_Lean_searchPathRef;
x_20 = lean::io_ref_set(x_19, x_18, x_15);
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
lean::dec(x_4);
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
lean::dec(x_8);
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
obj* _init_l_Lean_getBuiltinSearchPath___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("failed to locate builtin search path, please set LEAN_PATH");
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
x_7 = lean::string_append(x_4, x_6);
x_8 = l_Lean_getBuiltinSearchPath___closed__1;
x_9 = lean::string_append(x_7, x_8);
x_10 = lean::string_append(x_9, x_6);
x_11 = l_Lean_getBuiltinSearchPath___closed__2;
lean::inc(x_10);
x_12 = lean::string_append(x_10, x_11);
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
x_18 = lean::string_append(x_10, x_17);
x_19 = lean::string_append(x_18, x_6);
x_20 = l_Lean_getBuiltinSearchPath___closed__4;
x_21 = lean::string_append(x_19, x_20);
x_22 = lean::string_append(x_21, x_6);
x_23 = lean::string_append(x_22, x_11);
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
x_29 = l_Lean_getBuiltinSearchPath___closed__5;
lean::cnstr_set_tag(x_24, 1);
lean::cnstr_set(x_24, 0, x_29);
return x_24;
}
else
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_24, 1);
lean::inc(x_30);
lean::dec(x_24);
x_31 = l_Lean_getBuiltinSearchPath___closed__5;
x_32 = lean::alloc_cnstr(1, 2, 0);
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
x_35 = lean_io_realpath(x_23, x_24);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_5);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean_io_realpath(x_23, x_37);
return x_38;
}
}
}
else
{
uint8 x_39; 
lean::dec(x_23);
x_39 = !lean::is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
obj* x_40; obj* x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_24, 0);
x_41 = lean::cnstr_get(x_24, 1);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_24);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
obj* x_43; 
lean::dec(x_10);
x_43 = lean_io_realpath(x_12, x_13);
return x_43;
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; uint8 x_47; 
x_44 = lean::cnstr_get(x_13, 0);
x_45 = lean::cnstr_get(x_13, 1);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_13);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_45);
x_47 = lean::unbox(x_44);
lean::dec(x_44);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_12);
x_48 = l_Lean_getBuiltinSearchPath___closed__3;
x_49 = lean::string_append(x_10, x_48);
x_50 = lean::string_append(x_49, x_6);
x_51 = l_Lean_getBuiltinSearchPath___closed__4;
x_52 = lean::string_append(x_50, x_51);
x_53 = lean::string_append(x_52, x_6);
x_54 = lean::string_append(x_53, x_11);
x_55 = lean_io_is_dir(x_54, x_46);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; uint8 x_57; 
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_57 = lean::unbox(x_56);
lean::dec(x_56);
if (x_57 == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_54);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_59 = x_55;
} else {
 lean::dec_ref(x_55);
 x_59 = lean::box(0);
}
x_60 = l_Lean_getBuiltinSearchPath___closed__5;
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_61 = x_59;
 lean::cnstr_set_tag(x_61, 1);
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_55, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_63 = x_55;
} else {
 lean::dec_ref(x_55);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_5);
lean::cnstr_set(x_64, 1, x_62);
x_65 = lean_io_realpath(x_54, x_64);
return x_65;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_54);
x_66 = lean::cnstr_get(x_55, 0);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_55, 1);
lean::inc(x_67);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_68 = x_55;
} else {
 lean::dec_ref(x_55);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
}
else
{
obj* x_70; 
lean::dec(x_10);
x_70 = lean_io_realpath(x_12, x_46);
return x_70;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_12);
lean::dec(x_10);
x_71 = !lean::is_exclusive(x_13);
if (x_71 == 0)
{
return x_13;
}
else
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_13, 0);
x_73 = lean::cnstr_get(x_13, 1);
lean::inc(x_73);
lean::inc(x_72);
lean::dec(x_13);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_75 = lean::cnstr_get(x_2, 0);
x_76 = lean::cnstr_get(x_2, 1);
lean::inc(x_76);
lean::inc(x_75);
lean::dec(x_2);
x_77 = lean::box(0);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_76);
x_79 = l___private_init_lean_path_1__pathSep;
x_80 = lean::string_append(x_75, x_79);
x_81 = l_Lean_getBuiltinSearchPath___closed__1;
x_82 = lean::string_append(x_80, x_81);
x_83 = lean::string_append(x_82, x_79);
x_84 = l_Lean_getBuiltinSearchPath___closed__2;
lean::inc(x_83);
x_85 = lean::string_append(x_83, x_84);
x_86 = lean_io_is_dir(x_85, x_78);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; uint8 x_91; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_86, 1);
lean::inc(x_88);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_89 = x_86;
} else {
 lean::dec_ref(x_86);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_77);
lean::cnstr_set(x_90, 1, x_88);
x_91 = lean::unbox(x_87);
lean::dec(x_87);
if (x_91 == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_85);
x_92 = l_Lean_getBuiltinSearchPath___closed__3;
x_93 = lean::string_append(x_83, x_92);
x_94 = lean::string_append(x_93, x_79);
x_95 = l_Lean_getBuiltinSearchPath___closed__4;
x_96 = lean::string_append(x_94, x_95);
x_97 = lean::string_append(x_96, x_79);
x_98 = lean::string_append(x_97, x_84);
x_99 = lean_io_is_dir(x_98, x_90);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; uint8 x_101; 
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_101 = lean::unbox(x_100);
lean::dec(x_100);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_98);
x_102 = lean::cnstr_get(x_99, 1);
lean::inc(x_102);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_103 = x_99;
} else {
 lean::dec_ref(x_99);
 x_103 = lean::box(0);
}
x_104 = l_Lean_getBuiltinSearchPath___closed__5;
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_105 = x_103;
 lean::cnstr_set_tag(x_105, 1);
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
return x_105;
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_106 = lean::cnstr_get(x_99, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_107 = x_99;
} else {
 lean::dec_ref(x_99);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_77);
lean::cnstr_set(x_108, 1, x_106);
x_109 = lean_io_realpath(x_98, x_108);
return x_109;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_98);
x_110 = lean::cnstr_get(x_99, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_99, 1);
lean::inc(x_111);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 x_112 = x_99;
} else {
 lean::dec_ref(x_99);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
}
else
{
obj* x_114; 
lean::dec(x_83);
x_114 = lean_io_realpath(x_85, x_90);
return x_114;
}
}
else
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_85);
lean::dec(x_83);
x_115 = lean::cnstr_get(x_86, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_86, 1);
lean::inc(x_116);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 lean::cnstr_release(x_86, 1);
 x_117 = x_86;
} else {
 lean::dec_ref(x_86);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
uint8 x_119; 
x_119 = !lean::is_exclusive(x_2);
if (x_119 == 0)
{
return x_2;
}
else
{
obj* x_120; obj* x_121; obj* x_122; 
x_120 = lean::cnstr_get(x_2, 0);
x_121 = lean::cnstr_get(x_2, 1);
lean::inc(x_121);
lean::inc(x_120);
lean::dec(x_2);
x_122 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set(x_122, 1, x_121);
return x_122;
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
x_7 = lean::box(0);
lean::cnstr_set(x_3, 0, x_7);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::box(0);
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
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_3, 0);
lean::dec(x_12);
x_13 = !lean::is_exclusive(x_4);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_4, 0);
x_15 = l___private_init_lean_path_2__searchPathSep;
x_16 = l_String_split(x_14, x_15);
lean::cnstr_set(x_4, 0, x_16);
return x_3;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_4, 0);
lean::inc(x_17);
lean::dec(x_4);
x_18 = l___private_init_lean_path_2__searchPathSep;
x_19 = l_String_split(x_17, x_18);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_3, 0, x_20);
return x_3;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_3, 1);
lean::inc(x_21);
lean::dec(x_3);
x_22 = lean::cnstr_get(x_4, 0);
lean::inc(x_22);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_23 = x_4;
} else {
 lean::dec_ref(x_4);
 x_23 = lean::box(0);
}
x_24 = l___private_init_lean_path_2__searchPathSep;
x_25 = l_String_split(x_22, x_24);
if (lean::is_scalar(x_23)) {
 x_26 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_26 = x_23;
}
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_21);
return x_27;
}
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_3);
if (x_28 == 0)
{
return x_3;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_3, 0);
x_30 = lean::cnstr_get(x_3, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_3);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
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
namespace lean {
obj* init_search_path_core(obj* x_1, obj* x_2) {
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
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_3, 0);
x_6 = lean::box(0);
lean::cnstr_set(x_3, 0, x_6);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; 
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
x_10 = l_Lean_Name_toString___closed__1;
x_11 = lean_io_realpath(x_10, x_7);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_11, 0);
lean::cnstr_set(x_11, 0, x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_Lean_setSearchPath(x_16, x_11);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_11, 0);
x_19 = lean::cnstr_get(x_11, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_11);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_9);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_setSearchPath(x_23, x_20);
return x_24;
}
}
else
{
uint8 x_25; 
lean::dec(x_9);
x_25 = !lean::is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
x_26 = lean::cnstr_get(x_11, 0);
x_27 = lean::cnstr_get(x_11, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_11);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_7, 0);
x_30 = lean::cnstr_get(x_7, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_7);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_6);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_Lean_Name_toString___closed__1;
x_33 = lean_io_realpath(x_32, x_31);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_36 = x_33;
} else {
 lean::dec_ref(x_33);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_6);
lean::cnstr_set(x_37, 1, x_35);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_29);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_setSearchPath(x_40, x_37);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_29);
x_42 = lean::cnstr_get(x_33, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_33, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_44 = x_33;
} else {
 lean::dec_ref(x_33);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_7, 0);
x_48 = lean::cnstr_get(x_7, 1);
lean::inc(x_48);
lean::inc(x_47);
lean::dec(x_7);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_51; 
x_50 = lean::cnstr_get(x_5, 0);
lean::inc(x_50);
lean::dec(x_5);
x_51 = l_Lean_setSearchPath(x_50, x_3);
return x_51;
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_3, 0);
x_53 = lean::cnstr_get(x_3, 1);
lean::inc(x_53);
lean::inc(x_52);
lean::dec(x_3);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_53);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; 
x_56 = l_Lean_getBuiltinSearchPath(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_54);
lean::cnstr_set(x_60, 1, x_58);
x_61 = l_Lean_Name_toString___closed__1;
x_62 = lean_io_realpath(x_61, x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_62, 1);
lean::inc(x_64);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_65 = x_62;
} else {
 lean::dec_ref(x_62);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_54);
lean::cnstr_set(x_66, 1, x_64);
x_67 = lean::box(0);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_69, 0, x_57);
lean::cnstr_set(x_69, 1, x_68);
x_70 = l_Lean_setSearchPath(x_69, x_66);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_71 = lean::cnstr_get(x_62, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_62, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 lean::cnstr_release(x_62, 1);
 x_73 = x_62;
} else {
 lean::dec_ref(x_62);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_72);
return x_74;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_56, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_56, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_77 = x_56;
} else {
 lean::dec_ref(x_56);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
return x_78;
}
}
else
{
obj* x_79; obj* x_80; 
x_79 = lean::cnstr_get(x_52, 0);
lean::inc(x_79);
lean::dec(x_52);
x_80 = l_Lean_setSearchPath(x_79, x_55);
return x_80;
}
}
}
else
{
uint8 x_81; 
x_81 = !lean::is_exclusive(x_3);
if (x_81 == 0)
{
return x_3;
}
else
{
obj* x_82; obj* x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_3, 0);
x_83 = lean::cnstr_get(x_3, 1);
lean::inc(x_83);
lean::inc(x_82);
lean::dec(x_3);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
obj* x_85; obj* x_86; 
x_85 = lean::cnstr_get(x_1, 0);
lean::inc(x_85);
lean::dec(x_1);
x_86 = l_Lean_setSearchPathFromString(x_85, x_2);
return x_86;
}
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
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_3);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = lean::box(0);
lean::cnstr_set(x_4, 0, x_9);
return x_4;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::array_fget(x_2, x_3);
x_14 = l___private_init_lean_path_1__pathSep;
x_15 = lean::string_append(x_13, x_14);
lean::inc(x_15);
x_16 = lean::string_append(x_15, x_1);
x_17 = lean_io_file_exists(x_16, x_4);
if (lean::obj_tag(x_17) == 0)
{
obj* x_18; uint8 x_19; 
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
uint8 x_20; 
lean::dec(x_16);
lean::dec(x_15);
x_20 = !lean::is_exclusive(x_17);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_17, 0);
lean::dec(x_21);
x_22 = lean::box(0);
lean::cnstr_set(x_17, 0, x_22);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_3, x_23);
lean::dec(x_3);
x_3 = x_24;
x_4 = x_17;
goto _start;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_17, 1);
lean::inc(x_26);
lean::dec(x_17);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_3, x_29);
lean::dec(x_3);
x_3 = x_30;
x_4 = x_28;
goto _start;
}
}
else
{
uint8 x_32; 
lean::dec(x_3);
x_32 = !lean::is_exclusive(x_17);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_17, 0);
lean::dec(x_33);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_15);
lean::cnstr_set(x_34, 1, x_16);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_17, 0, x_35);
return x_17;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_17, 1);
lean::inc(x_36);
lean::dec(x_17);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_15);
lean::cnstr_set(x_37, 1, x_16);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8 x_40; 
lean::dec(x_16);
lean::dec(x_15);
lean::dec(x_3);
x_40 = !lean::is_exclusive(x_17);
if (x_40 == 0)
{
return x_17;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_17, 0);
x_42 = lean::cnstr_get(x_17, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_17);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
obj* l_Lean_findFile(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_searchPathRef;
x_4 = lean::io_ref_get(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean::box(0);
lean::cnstr_set(x_4, 0, x_7);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_1, x_6, x_8, x_4);
lean::dec(x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_4);
x_12 = lean::box(0);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_1, x_10, x_14, x_13);
lean::dec(x_10);
return x_15;
}
}
else
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_4);
if (x_16 == 0)
{
return x_4;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_4, 0);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_4);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
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
obj* l_Array_mfindAux___main___at_Lean_findFile___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mfindAux___main___at_Lean_findFile___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_findFile___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_findFile(x_1, x_2);
lean::dec(x_1);
return x_3;
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
x_9 = lean::string_append(x_7, x_8);
x_10 = lean::string_append(x_9, x_4);
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
x_4 = lean::nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_sub(x_2, x_5);
x_7 = l_Lean_addRel___main(x_1, x_6);
lean::dec(x_6);
x_8 = l___private_init_lean_path_1__pathSep;
x_9 = lean::string_append(x_7, x_8);
x_10 = l_Lean_getBuiltinSearchPath___closed__1;
x_11 = lean::string_append(x_9, x_10);
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
obj* x_1; uint32 x_2; obj* x_3; 
x_1 = l_String_splitAux___main___closed__1;
x_2 = l_System_FilePath_extSeparator;
x_3 = lean::string_push(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_findLeanFile___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("module '");
return x_1;
}
}
obj* _init_l_Lean_findLeanFile___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("' not found");
return x_1;
}
}
obj* l_Lean_findLeanFile(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_Lean_modNameToFileName___main(x_2);
x_6 = l_Lean_findLeanFile___closed__1;
x_7 = lean::string_append(x_5, x_6);
x_8 = lean::string_append(x_7, x_3);
if (lean::obj_tag(x_1) == 0)
{
obj* x_9; 
x_9 = l_Lean_findFile(x_8, x_4);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_9, 0);
lean::dec(x_12);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_2);
x_15 = l_Lean_findLeanFile___closed__2;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_17 = l_Lean_findLeanFile___closed__3;
x_18 = lean::string_append(x_16, x_17);
lean::cnstr_set_tag(x_9, 1);
lean::cnstr_set(x_9, 0, x_18);
return x_9;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
x_20 = l_Lean_Name_toString___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_2);
x_22 = l_Lean_findLeanFile___closed__2;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_24 = l_Lean_findLeanFile___closed__3;
x_25 = lean::string_append(x_23, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_19);
return x_26;
}
}
else
{
uint8 x_27; 
lean::dec(x_2);
x_27 = !lean::is_exclusive(x_9);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; uint8 x_31; 
x_28 = lean::cnstr_get(x_9, 0);
lean::dec(x_28);
x_29 = lean::cnstr_get(x_10, 0);
lean::inc(x_29);
lean::dec(x_10);
x_30 = lean::box(0);
lean::cnstr_set(x_9, 0, x_30);
x_31 = !lean::is_exclusive(x_29);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_29, 0);
x_33 = lean::cnstr_get(x_29, 1);
x_34 = lean_io_realpath(x_33, x_9);
if (lean::obj_tag(x_34) == 0)
{
uint8 x_35; 
x_35 = !lean::is_exclusive(x_34);
if (x_35 == 0)
{
obj* x_36; 
x_36 = lean::cnstr_get(x_34, 0);
lean::cnstr_set(x_29, 1, x_36);
lean::cnstr_set(x_34, 0, x_29);
return x_34;
}
else
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_34, 0);
x_38 = lean::cnstr_get(x_34, 1);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_34);
lean::cnstr_set(x_29, 1, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8 x_40; 
lean::free_heap_obj(x_29);
lean::dec(x_32);
x_40 = !lean::is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
obj* x_41; obj* x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_34, 0);
x_42 = lean::cnstr_get(x_34, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_34);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
obj* x_44; obj* x_45; obj* x_46; 
x_44 = lean::cnstr_get(x_29, 0);
x_45 = lean::cnstr_get(x_29, 1);
lean::inc(x_45);
lean::inc(x_44);
lean::dec(x_29);
x_46 = lean_io_realpath(x_45, x_9);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_49 = x_46;
} else {
 lean::dec_ref(x_46);
 x_49 = lean::box(0);
}
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_47);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_48);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_44);
x_52 = lean::cnstr_get(x_46, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_46, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_54 = x_46;
} else {
 lean::dec_ref(x_46);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_56 = lean::cnstr_get(x_9, 1);
lean::inc(x_56);
lean::dec(x_9);
x_57 = lean::cnstr_get(x_10, 0);
lean::inc(x_57);
lean::dec(x_10);
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_56);
x_60 = lean::cnstr_get(x_57, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
} else {
 lean::dec_ref(x_57);
 x_62 = lean::box(0);
}
x_63 = lean_io_realpath(x_61, x_59);
if (lean::obj_tag(x_63) == 0)
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_66 = x_63;
} else {
 lean::dec_ref(x_63);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_62;
}
lean::cnstr_set(x_67, 0, x_60);
lean::cnstr_set(x_67, 1, x_64);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_65);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_62);
lean::dec(x_60);
x_69 = lean::cnstr_get(x_63, 0);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_63, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 lean::cnstr_release(x_63, 1);
 x_71 = x_63;
} else {
 lean::dec_ref(x_63);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
}
}
}
else
{
uint8 x_73; 
lean::dec(x_2);
x_73 = !lean::is_exclusive(x_9);
if (x_73 == 0)
{
return x_9;
}
else
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_9, 0);
x_75 = lean::cnstr_get(x_9, 1);
lean::inc(x_75);
lean::inc(x_74);
lean::dec(x_9);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_1, 0);
x_78 = l_Lean_Name_toString___closed__1;
x_79 = lean_io_realpath(x_78, x_4);
if (lean::obj_tag(x_79) == 0)
{
uint8 x_80; 
x_80 = !lean::is_exclusive(x_79);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_81 = lean::cnstr_get(x_79, 0);
x_82 = lean::box(0);
lean::cnstr_set(x_79, 0, x_82);
x_83 = l_Lean_addRel___main(x_81, x_77);
x_84 = l___private_init_lean_path_1__pathSep;
x_85 = lean::string_append(x_83, x_84);
x_86 = lean::string_append(x_85, x_8);
lean::dec(x_8);
x_87 = lean_io_file_exists(x_86, x_79);
if (lean::obj_tag(x_87) == 0)
{
obj* x_88; uint8 x_89; 
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_89 = lean::unbox(x_88);
lean::dec(x_88);
if (x_89 == 0)
{
uint8 x_90; 
lean::dec(x_86);
lean::dec(x_81);
x_90 = !lean::is_exclusive(x_87);
if (x_90 == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_91 = lean::cnstr_get(x_87, 0);
lean::dec(x_91);
x_92 = l_Lean_Name_toStringWithSep___main(x_78, x_2);
x_93 = l_Lean_findLeanFile___closed__2;
x_94 = lean::string_append(x_93, x_92);
lean::dec(x_92);
x_95 = l_Lean_findLeanFile___closed__3;
x_96 = lean::string_append(x_94, x_95);
lean::cnstr_set_tag(x_87, 1);
lean::cnstr_set(x_87, 0, x_96);
return x_87;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_97 = lean::cnstr_get(x_87, 1);
lean::inc(x_97);
lean::dec(x_87);
x_98 = l_Lean_Name_toStringWithSep___main(x_78, x_2);
x_99 = l_Lean_findLeanFile___closed__2;
x_100 = lean::string_append(x_99, x_98);
lean::dec(x_98);
x_101 = l_Lean_findLeanFile___closed__3;
x_102 = lean::string_append(x_100, x_101);
x_103 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_97);
return x_103;
}
}
else
{
uint8 x_104; 
lean::dec(x_2);
x_104 = !lean::is_exclusive(x_87);
if (x_104 == 0)
{
obj* x_105; obj* x_106; 
x_105 = lean::cnstr_get(x_87, 0);
lean::dec(x_105);
lean::cnstr_set(x_87, 0, x_82);
x_106 = lean_io_realpath(x_86, x_87);
if (lean::obj_tag(x_106) == 0)
{
uint8 x_107; 
x_107 = !lean::is_exclusive(x_106);
if (x_107 == 0)
{
obj* x_108; obj* x_109; 
x_108 = lean::cnstr_get(x_106, 0);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_81);
lean::cnstr_set(x_109, 1, x_108);
lean::cnstr_set(x_106, 0, x_109);
return x_106;
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_110 = lean::cnstr_get(x_106, 0);
x_111 = lean::cnstr_get(x_106, 1);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_106);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_81);
lean::cnstr_set(x_112, 1, x_110);
x_113 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8 x_114; 
lean::dec(x_81);
x_114 = !lean::is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
obj* x_115; obj* x_116; obj* x_117; 
x_115 = lean::cnstr_get(x_106, 0);
x_116 = lean::cnstr_get(x_106, 1);
lean::inc(x_116);
lean::inc(x_115);
lean::dec(x_106);
x_117 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_117, 0, x_115);
lean::cnstr_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
obj* x_118; obj* x_119; obj* x_120; 
x_118 = lean::cnstr_get(x_87, 1);
lean::inc(x_118);
lean::dec(x_87);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_82);
lean::cnstr_set(x_119, 1, x_118);
x_120 = lean_io_realpath(x_86, x_119);
if (lean::obj_tag(x_120) == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_122 = lean::cnstr_get(x_120, 1);
lean::inc(x_122);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_123 = x_120;
} else {
 lean::dec_ref(x_120);
 x_123 = lean::box(0);
}
x_124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_124, 0, x_81);
lean::cnstr_set(x_124, 1, x_121);
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_81);
x_126 = lean::cnstr_get(x_120, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_120, 1);
lean::inc(x_127);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 lean::cnstr_release(x_120, 1);
 x_128 = x_120;
} else {
 lean::dec_ref(x_120);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
lean::cnstr_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
uint8 x_130; 
lean::dec(x_86);
lean::dec(x_81);
lean::dec(x_2);
x_130 = !lean::is_exclusive(x_87);
if (x_130 == 0)
{
return x_87;
}
else
{
obj* x_131; obj* x_132; obj* x_133; 
x_131 = lean::cnstr_get(x_87, 0);
x_132 = lean::cnstr_get(x_87, 1);
lean::inc(x_132);
lean::inc(x_131);
lean::dec(x_87);
x_133 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_133, 0, x_131);
lean::cnstr_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_134 = lean::cnstr_get(x_79, 0);
x_135 = lean::cnstr_get(x_79, 1);
lean::inc(x_135);
lean::inc(x_134);
lean::dec(x_79);
x_136 = lean::box(0);
x_137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_135);
x_138 = l_Lean_addRel___main(x_134, x_77);
x_139 = l___private_init_lean_path_1__pathSep;
x_140 = lean::string_append(x_138, x_139);
x_141 = lean::string_append(x_140, x_8);
lean::dec(x_8);
x_142 = lean_io_file_exists(x_141, x_137);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; uint8 x_144; 
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_144 = lean::unbox(x_143);
lean::dec(x_143);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_141);
lean::dec(x_134);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_146 = x_142;
} else {
 lean::dec_ref(x_142);
 x_146 = lean::box(0);
}
x_147 = l_Lean_Name_toStringWithSep___main(x_78, x_2);
x_148 = l_Lean_findLeanFile___closed__2;
x_149 = lean::string_append(x_148, x_147);
lean::dec(x_147);
x_150 = l_Lean_findLeanFile___closed__3;
x_151 = lean::string_append(x_149, x_150);
if (lean::is_scalar(x_146)) {
 x_152 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_152 = x_146;
 lean::cnstr_set_tag(x_152, 1);
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_145);
return x_152;
}
else
{
obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
lean::dec(x_2);
x_153 = lean::cnstr_get(x_142, 1);
lean::inc(x_153);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_154 = x_142;
} else {
 lean::dec_ref(x_142);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_136);
lean::cnstr_set(x_155, 1, x_153);
x_156 = lean_io_realpath(x_141, x_155);
if (lean::obj_tag(x_156) == 0)
{
obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; 
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_156, 1);
lean::inc(x_158);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_159 = x_156;
} else {
 lean::dec_ref(x_156);
 x_159 = lean::box(0);
}
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_134);
lean::cnstr_set(x_160, 1, x_157);
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
lean::dec(x_134);
x_162 = lean::cnstr_get(x_156, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_156, 1);
lean::inc(x_163);
if (lean::is_exclusive(x_156)) {
 lean::cnstr_release(x_156, 0);
 lean::cnstr_release(x_156, 1);
 x_164 = x_156;
} else {
 lean::dec_ref(x_156);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
lean::cnstr_set(x_165, 1, x_163);
return x_165;
}
}
}
else
{
obj* x_166; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_141);
lean::dec(x_134);
lean::dec(x_2);
x_166 = lean::cnstr_get(x_142, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_142, 1);
lean::inc(x_167);
if (lean::is_exclusive(x_142)) {
 lean::cnstr_release(x_142, 0);
 lean::cnstr_release(x_142, 1);
 x_168 = x_142;
} else {
 lean::dec_ref(x_142);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
uint8 x_170; 
lean::dec(x_8);
lean::dec(x_2);
x_170 = !lean::is_exclusive(x_79);
if (x_170 == 0)
{
return x_79;
}
else
{
obj* x_171; obj* x_172; obj* x_173; 
x_171 = lean::cnstr_get(x_79, 0);
x_172 = lean::cnstr_get(x_79, 1);
lean::inc(x_172);
lean::inc(x_171);
lean::dec(x_79);
x_173 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_173, 0, x_171);
lean::cnstr_set(x_173, 1, x_172);
return x_173;
}
}
}
}
}
obj* l_Lean_findLeanFile___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_findLeanFile(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_5;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::box(0);
x_4 = l_Lean_findOLean___closed__1;
x_5 = l_Lean_findLeanFile(x_3, x_1, x_4, x_2);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
lean::cnstr_set(x_5, 0, x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_5, 0);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_Lean_findLean(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_getBuiltinSearchPath___closed__4;
x_5 = l_Lean_findLeanFile(x_1, x_2, x_4, x_3);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
lean::cnstr_set(x_5, 0, x_8);
return x_5;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::inc(x_9);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
lean::dec(x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8 x_13; 
x_13 = !lean::is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_5, 0);
x_15 = lean::cnstr_get(x_5, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_5);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
}
}
obj* l_Lean_findLean___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_findLean(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
if (io_result_is_error(w)) return w;
w = initialize_init_system_io(w);
if (io_result_is_error(w)) return w;
w = initialize_init_system_filepath(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_control_combinators(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_name(w);
if (io_result_is_error(w)) return w;
l___private_init_lean_path_1__pathSep___closed__1 = _init_l___private_init_lean_path_1__pathSep___closed__1();
lean::mark_persistent(l___private_init_lean_path_1__pathSep___closed__1);
l___private_init_lean_path_1__pathSep = _init_l___private_init_lean_path_1__pathSep();
lean::mark_persistent(l___private_init_lean_path_1__pathSep);
l___private_init_lean_path_2__searchPathSep___closed__1 = _init_l___private_init_lean_path_2__searchPathSep___closed__1();
lean::mark_persistent(l___private_init_lean_path_2__searchPathSep___closed__1);
l___private_init_lean_path_2__searchPathSep = _init_l___private_init_lean_path_2__searchPathSep();
lean::mark_persistent(l___private_init_lean_path_2__searchPathSep);
w = l_Lean_mkSearchPathRef(w);
if (io_result_is_error(w)) return w;
l_Lean_searchPathRef = io_result_get_value(w);
lean::mark_persistent(l_Lean_searchPathRef);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__1);
l_Lean_getBuiltinSearchPath___closed__2 = _init_l_Lean_getBuiltinSearchPath___closed__2();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__2);
l_Lean_getBuiltinSearchPath___closed__3 = _init_l_Lean_getBuiltinSearchPath___closed__3();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__3);
l_Lean_getBuiltinSearchPath___closed__4 = _init_l_Lean_getBuiltinSearchPath___closed__4();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__4);
l_Lean_getBuiltinSearchPath___closed__5 = _init_l_Lean_getBuiltinSearchPath___closed__5();
lean::mark_persistent(l_Lean_getBuiltinSearchPath___closed__5);
l_Lean_getSearchPathFromEnv___closed__1 = _init_l_Lean_getSearchPathFromEnv___closed__1();
lean::mark_persistent(l_Lean_getSearchPathFromEnv___closed__1);
l_Lean_findLeanFile___closed__1 = _init_l_Lean_findLeanFile___closed__1();
lean::mark_persistent(l_Lean_findLeanFile___closed__1);
l_Lean_findLeanFile___closed__2 = _init_l_Lean_findLeanFile___closed__2();
lean::mark_persistent(l_Lean_findLeanFile___closed__2);
l_Lean_findLeanFile___closed__3 = _init_l_Lean_findLeanFile___closed__3();
lean::mark_persistent(l_Lean_findLeanFile___closed__3);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean::mark_persistent(l_Lean_findOLean___closed__1);
return w;
}
