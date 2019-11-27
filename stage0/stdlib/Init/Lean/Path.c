// Lean compiler output
// Module: Init.Lean.Path
// Imports: Init.System.IO Init.System.FilePath Init.Data.Array Init.Data.List.Control Init.Lean.Name Init.Data.HashMap Init.Data.Nat.Control
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
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_getBuiltinSearchPath___closed__6;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_parseSearchPath___spec__3(lean_object*, lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_searchPathRef;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
lean_object* l_Lean_mkSearchPathRef(lean_object*);
lean_object* l_Lean_parseSearchPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_findOLean___spec__2(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__3;
lean_object* l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Path_1__pathSep;
lean_object* l_Lean_modPathToFilePath___main___closed__2;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__1;
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_findOLean___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_findAtSearchPath(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__1;
lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__1;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_System_FilePath_normalizePath(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_findOLean___closed__2;
lean_object* l_Lean_modPathToFilePath___boxed(lean_object*);
lean_object* l_Lean_modPathToFilePath___main___boxed(lean_object*);
lean_object* l_Lean_normalizeModuleName___closed__2;
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__1;
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__2;
lean_object* l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_findOLean___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_splitAtRoot(lean_object*);
lean_object* l_Lean_findOLean___closed__1;
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2;
lean_object* l___private_Init_Lean_Path_1__pathSep___closed__1;
lean_object* l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_findAtSearchPath___spec__3(lean_object*);
lean_object* l_Lean_normalizeModuleName___closed__1;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__2;
lean_object* l_Lean_getBuiltinSearchPath___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_mkSearchPathRef___closed__1;
lean_object* l_mkHashMap___at_Lean_mkSearchPathRef___spec__1(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_findOLean___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Char_DecidableEq(uint32_t, uint32_t);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseSearchPath(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1;
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object*);
lean_object* l_IO_isDir___at_Lean_getBuiltinSearchPath___spec__3(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3;
lean_object* lean_string_length(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath(lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_splitAtRoot___main___closed__1;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_String_drop(lean_object*, lean_object*);
lean_object* l_Lean_splitAtRoot___main(lean_object*);
extern lean_object* l_HashMap_Inhabited___closed__1;
lean_object* l_Lean_getBuiltinSearchPath___closed__3;
extern lean_object* l_String_Inhabited;
lean_object* l_Lean_splitAtRoot___main___closed__2;
lean_object* lean_normalize_module_name(lean_object*);
size_t lean_string_hash(lean_object*);
lean_object* l_IO_realPath___at_Lean_realPathNormalized___spec__1(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2(lean_object*, lean_object*);
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
lean_object* l_mkHashMap___at_Lean_mkSearchPathRef___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_mkSearchPathRef___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_mkSearchPathRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_mkSearchPathRef___closed__1;
x_3 = lean_io_mk_ref(x_2, x_1);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_string_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
lean_inc(x_4);
x_7 = lean_string_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
lean_inc(x_12);
x_16 = lean_string_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_parseSearchPath___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_string_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_string_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
lean_inc(x_2);
x_8 = lean_string_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_parseSearchPath___spec__3(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
lean_inc(x_2);
x_25 = lean_string_hash(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_parseSearchPath___spec__3(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__6(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed search path entry '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', should be of form 'pkg=path'");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=");
return x_1;
}
}
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_14 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3;
lean_inc(x_5);
x_15 = l_String_splitOn(x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_box(0);
x_7 = x_16;
goto block_13;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_box(0);
x_7 = x_18;
goto block_13;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_1, x_20, x_21);
x_1 = x_22;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_box(0);
x_7 = x_24;
goto block_13;
}
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_8 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
}
lean_object* l_Lean_parseSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_split___at_System_FilePath_splitSearchPath___spec__2(x_1);
x_5 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__7(x_2, x_4, x_3);
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
lean_object* l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
x_1 = lean_mk_string("src");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lib");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lean");
return x_1;
}
}
lean_object* _init_l_Lean_getBuiltinSearchPath___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("library");
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Init_Lean_Path_1__pathSep;
x_6 = lean_string_append(x_3, x_5);
x_7 = l_Lean_getBuiltinSearchPath___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_5);
x_10 = l_Lean_getBuiltinSearchPath___closed__2;
lean_inc(x_9);
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_5);
x_13 = l_Lean_getBuiltinSearchPath___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_io_is_dir(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_unbox(x_16);
lean_dec(x_16);
x_20 = l_Bool_DecidableEq(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_14);
x_21 = l_Lean_getBuiltinSearchPath___closed__4;
x_22 = lean_string_append(x_9, x_21);
x_23 = lean_string_append(x_22, x_5);
x_24 = l_Lean_getBuiltinSearchPath___closed__5;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_5);
x_27 = l_Lean_getBuiltinSearchPath___closed__6;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_5);
x_30 = lean_string_append(x_29, x_13);
x_31 = lean_io_is_dir(x_30, x_17);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_unbox(x_33);
lean_dec(x_33);
x_36 = l_Bool_DecidableEq(x_35, x_18);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_30);
x_37 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
else
{
lean_object* x_38; 
lean_free_object(x_31);
x_38 = l_Lean_realPathNormalized(x_30, x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_HashMap_Inhabited___closed__1;
x_42 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_41, x_13, x_40);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = l_HashMap_Inhabited___closed__1;
x_46 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_45, x_13, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_55 = l_Bool_DecidableEq(x_54, x_18);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_30);
x_56 = l_HashMap_Inhabited___closed__1;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = l_Lean_realPathNormalized(x_30, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = l_HashMap_Inhabited___closed__1;
x_63 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_62, x_13, x_59);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_30);
x_69 = !lean_is_exclusive(x_31);
if (x_69 == 0)
{
return x_31;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_31, 0);
x_71 = lean_ctor_get(x_31, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_31);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_9);
x_73 = l_Lean_realPathNormalized(x_14, x_17);
if (lean_obj_tag(x_73) == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_HashMap_Inhabited___closed__1;
x_77 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_76, x_13, x_75);
lean_ctor_set(x_73, 0, x_77);
return x_73;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_73, 0);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_73);
x_80 = l_HashMap_Inhabited___closed__1;
x_81 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__1(x_80, x_13, x_78);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_73);
if (x_83 == 0)
{
return x_73;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_73, 0);
x_85 = lean_ctor_get(x_73, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_73);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_14);
lean_dec(x_9);
x_87 = !lean_is_exclusive(x_15);
if (x_87 == 0)
{
return x_15;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_15, 0);
x_89 = lean_ctor_get(x_15, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_15);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_2);
if (x_91 == 0)
{
return x_2;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_2, 0);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_2);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = l_HashMap_Inhabited___closed__1;
x_21 = l_Lean_parseSearchPath(x_19, x_20, x_2);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_searchPathRef;
x_25 = lean_io_ref_set(x_24, x_22, x_23);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* _init_l_Lean_modPathToFilePath___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Lean.Path");
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
x_2 = lean_unsigned_to_nat(81u);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_6 = l_Lean_modPathToFilePath___main(x_3);
x_7 = l___private_Init_Lean_Path_1__pathSep;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_4);
return x_9;
}
}
default: 
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_String_Inhabited;
x_13 = l_Lean_modPathToFilePath___main___closed__3;
x_14 = lean_panic_fn(x_13);
return x_14;
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
lean_object* _init_l_Lean_splitAtRoot___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_Inhabited;
x_2 = l_Lean_Name_inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_splitAtRoot___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_modPathToFilePath___main___closed__1;
x_2 = lean_unsigned_to_nat(89u);
x_3 = lean_unsigned_to_nat(20u);
x_4 = l_Lean_modPathToFilePath___main___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_splitAtRoot___main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_2);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
x_4 = x_15;
goto block_13;
}
block_13:
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_4);
x_5 = l_Lean_splitAtRoot___main(x_2);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_name_mk_string(x_7, x_3);
lean_ctor_set(x_5, 1, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_name_mk_string(x_10, x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = l_Lean_splitAtRoot___main___closed__1;
x_17 = l_Lean_splitAtRoot___main___closed__2;
x_18 = lean_panic_fn(x_17);
return x_18;
}
}
}
lean_object* l_Lean_splitAtRoot(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_splitAtRoot___main(x_1);
return x_2;
}
}
lean_object* l_AssocList_find___main___at_Lean_findOLean___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_string_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find___at_Lean_findOLean___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
lean_inc(x_2);
x_5 = lean_string_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_findOLean___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
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
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_splitAtRoot___main(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = l_HashMapImp_find___at_Lean_findOLean___spec__1(x_6, x_8);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_11 = l_Lean_findOLean___closed__1;
x_12 = lean_string_append(x_11, x_8);
lean_dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean_string_append(x_12, x_13);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l___private_Init_Lean_Path_1__pathSep;
x_17 = lean_string_append(x_15, x_16);
x_18 = l_Lean_modPathToFilePath___main(x_9);
lean_dec(x_9);
x_19 = lean_string_append(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_findOLean___closed__2;
x_21 = lean_string_append(x_19, x_20);
lean_ctor_set(x_4, 0, x_21);
return x_4;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_24 = l_Lean_splitAtRoot___main(x_1);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_HashMapImp_find___at_Lean_findOLean___spec__1(x_22, x_25);
lean_dec(x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
x_28 = l_Lean_findOLean___closed__1;
x_29 = lean_string_append(x_28, x_25);
lean_dec(x_25);
x_30 = l_Char_HasRepr___closed__1;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_25);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l___private_Init_Lean_Path_1__pathSep;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_Lean_modPathToFilePath___main(x_26);
lean_dec(x_26);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Lean_findOLean___closed__2;
x_39 = lean_string_append(x_37, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_23);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
return x_4;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_4, 0);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_4);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_findOLean___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_findOLean___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_findOLean___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_findOLean___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l_Lean_realPathNormalized(x_7, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_String_isPrefixOf(x_10, x_1);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
x_3 = x_8;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
x_2 = x_17;
x_3 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_3, x_4);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_13 = l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1(x_1, x_5, x_10, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_4 = x_12;
x_5 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l_List_map___main___at_Lean_findAtSearchPath___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___main___at_Lean_findAtSearchPath___spec__3(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___main___at_Lean_findAtSearchPath___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
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
x_1 = lean_mk_string("' is contained in multiple packages: ");
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_searchPathRef;
x_7 = lean_io_ref_get(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2(x_4, x_8, x_11, x_12, x_10, x_9);
lean_dec(x_11);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_13, 0);
lean_dec(x_31);
x_32 = l_Lean_findAtSearchPath___closed__1;
x_33 = lean_string_append(x_32, x_4);
lean_dec(x_4);
x_34 = l_Lean_findAtSearchPath___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = l_List_map___main___at_Lean_findAtSearchPath___spec__3(x_14);
x_37 = l_List_reprAux___main___rarg___closed__1;
x_38 = l_String_intercalate(x_37, x_36);
x_39 = lean_string_append(x_35, x_38);
lean_dec(x_38);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_39);
return x_13;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_dec(x_13);
x_41 = l_Lean_findAtSearchPath___closed__1;
x_42 = lean_string_append(x_41, x_4);
lean_dec(x_4);
x_43 = l_Lean_findAtSearchPath___closed__2;
x_44 = lean_string_append(x_42, x_43);
x_45 = l_List_map___main___at_Lean_findAtSearchPath___spec__3(x_14);
x_46 = l_List_reprAux___main___rarg___closed__1;
x_47 = l_String_intercalate(x_46, x_45);
x_48 = lean_string_append(x_44, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
return x_7;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_3);
if (x_58 == 0)
{
return x_3;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_3);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
x_1 = lean_mk_string("' to module name, extension is missing");
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
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_3, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_realPathNormalized(x_1, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint32_t x_21; uint32_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint32_t x_26; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_string_length(x_14);
lean_dec(x_14);
x_19 = l_String_drop(x_17, x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_get(x_19, x_20);
x_22 = l_System_FilePath_pathSeparator;
x_23 = l_Char_DecidableEq(x_21, x_22);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
x_26 = 46;
if (x_25 == 0)
{
lean_object* x_27; 
x_27 = l_String_revPosOf(x_19, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
lean_dec(x_13);
x_28 = l_Lean_moduleNameOfFileName___closed__1;
x_29 = lean_string_append(x_28, x_17);
lean_dec(x_17);
x_30 = l_Lean_moduleNameOfFileName___closed__2;
x_31 = lean_string_append(x_29, x_30);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
uint8_t x_32; 
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_string_utf8_extract(x_19, x_20, x_33);
lean_dec(x_33);
lean_dec(x_19);
x_35 = l___private_Init_Lean_Path_1__pathSep;
x_36 = l_String_splitOn(x_34, x_35);
x_37 = lean_box(0);
x_38 = lean_name_mk_string(x_37, x_13);
x_39 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_38, x_36);
lean_ctor_set(x_27, 0, x_39);
lean_ctor_set(x_15, 0, x_27);
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_string_utf8_extract(x_19, x_20, x_40);
lean_dec(x_40);
lean_dec(x_19);
x_42 = l___private_Init_Lean_Path_1__pathSep;
x_43 = l_String_splitOn(x_41, x_42);
x_44 = lean_box(0);
x_45 = lean_name_mk_string(x_44, x_13);
x_46 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_45, x_43);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_15, 0, x_47);
return x_15;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = l_String_drop(x_19, x_48);
lean_dec(x_19);
x_50 = l_String_revPosOf(x_49, x_26);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
lean_dec(x_13);
x_51 = l_Lean_moduleNameOfFileName___closed__1;
x_52 = lean_string_append(x_51, x_17);
lean_dec(x_17);
x_53 = l_Lean_moduleNameOfFileName___closed__2;
x_54 = lean_string_append(x_52, x_53);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_54);
return x_15;
}
else
{
uint8_t x_55; 
lean_dec(x_17);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_string_utf8_extract(x_49, x_20, x_56);
lean_dec(x_56);
lean_dec(x_49);
x_58 = l___private_Init_Lean_Path_1__pathSep;
x_59 = l_String_splitOn(x_57, x_58);
x_60 = lean_box(0);
x_61 = lean_name_mk_string(x_60, x_13);
x_62 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_61, x_59);
lean_ctor_set(x_50, 0, x_62);
lean_ctor_set(x_15, 0, x_50);
return x_15;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
lean_dec(x_50);
x_64 = lean_string_utf8_extract(x_49, x_20, x_63);
lean_dec(x_63);
lean_dec(x_49);
x_65 = l___private_Init_Lean_Path_1__pathSep;
x_66 = l_String_splitOn(x_64, x_65);
x_67 = lean_box(0);
x_68 = lean_name_mk_string(x_67, x_13);
x_69 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_68, x_66);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_15, 0, x_70);
return x_15;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint32_t x_76; uint32_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint32_t x_81; 
x_71 = lean_ctor_get(x_15, 0);
x_72 = lean_ctor_get(x_15, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_15);
x_73 = lean_string_length(x_14);
lean_dec(x_14);
x_74 = l_String_drop(x_71, x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_string_utf8_get(x_74, x_75);
x_77 = l_System_FilePath_pathSeparator;
x_78 = l_Char_DecidableEq(x_76, x_77);
x_79 = 1;
x_80 = l_Bool_DecidableEq(x_78, x_79);
x_81 = 46;
if (x_80 == 0)
{
lean_object* x_82; 
x_82 = l_String_revPosOf(x_74, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_74);
lean_dec(x_13);
x_83 = l_Lean_moduleNameOfFileName___closed__1;
x_84 = lean_string_append(x_83, x_71);
lean_dec(x_71);
x_85 = l_Lean_moduleNameOfFileName___closed__2;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_72);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_71);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_89 = x_82;
} else {
 lean_dec_ref(x_82);
 x_89 = lean_box(0);
}
x_90 = lean_string_utf8_extract(x_74, x_75, x_88);
lean_dec(x_88);
lean_dec(x_74);
x_91 = l___private_Init_Lean_Path_1__pathSep;
x_92 = l_String_splitOn(x_90, x_91);
x_93 = lean_box(0);
x_94 = lean_name_mk_string(x_93, x_13);
x_95 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_94, x_92);
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_89;
}
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_72);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_unsigned_to_nat(1u);
x_99 = l_String_drop(x_74, x_98);
lean_dec(x_74);
x_100 = l_String_revPosOf(x_99, x_81);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_99);
lean_dec(x_13);
x_101 = l_Lean_moduleNameOfFileName___closed__1;
x_102 = lean_string_append(x_101, x_71);
lean_dec(x_71);
x_103 = l_Lean_moduleNameOfFileName___closed__2;
x_104 = lean_string_append(x_102, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_72);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_71);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_107 = x_100;
} else {
 lean_dec_ref(x_100);
 x_107 = lean_box(0);
}
x_108 = lean_string_utf8_extract(x_99, x_75, x_106);
lean_dec(x_106);
lean_dec(x_99);
x_109 = l___private_Init_Lean_Path_1__pathSep;
x_110 = l_String_splitOn(x_108, x_109);
x_111 = lean_box(0);
x_112 = lean_name_mk_string(x_111, x_13);
x_113 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_112, x_110);
if (lean_is_scalar(x_107)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_107;
}
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_72);
return x_115;
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_14);
lean_dec(x_13);
x_116 = !lean_is_exclusive(x_15);
if (x_116 == 0)
{
return x_15;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_15, 0);
x_118 = lean_ctor_get(x_15, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_15);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_3);
if (x_120 == 0)
{
return x_3;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_3, 0);
x_122 = lean_ctor_get(x_3, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_3);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
lean_object* _init_l_Lean_normalizeModuleName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Default");
return x_1;
}
}
lean_object* _init_l_Lean_normalizeModuleName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_normalizeModuleName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* lean_normalize_module_name(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_name_mk_string(x_4, x_3);
x_6 = l_Lean_normalizeModuleName___closed__2;
x_7 = l_Lean_Name_append___main(x_5, x_6);
lean_dec(x_5);
return x_7;
}
else
{
lean_dec(x_2);
return x_1;
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_System_IO(lean_object*);
lean_object* initialize_Init_System_FilePath(lean_object*);
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Data_List_Control(lean_object*);
lean_object* initialize_Init_Lean_Name(lean_object*);
lean_object* initialize_Init_Data_HashMap(lean_object*);
lean_object* initialize_Init_Data_Nat_Control(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Path(lean_object* w) {
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
res = initialize_Init_Lean_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_HashMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Path_1__pathSep___closed__1 = _init_l___private_Init_Lean_Path_1__pathSep___closed__1();
lean_mark_persistent(l___private_Init_Lean_Path_1__pathSep___closed__1);
l___private_Init_Lean_Path_1__pathSep = _init_l___private_Init_Lean_Path_1__pathSep();
lean_mark_persistent(l___private_Init_Lean_Path_1__pathSep);
l_Lean_mkSearchPathRef___closed__1 = _init_l_Lean_mkSearchPathRef___closed__1();
lean_mark_persistent(l_Lean_mkSearchPathRef___closed__1);
res = l_Lean_mkSearchPathRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__1);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__2);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__7___closed__3);
l_Lean_getBuiltinSearchPath___closed__1 = _init_l_Lean_getBuiltinSearchPath___closed__1();
lean_mark_persistent(l_Lean_getBuiltinSearchPath___closed__1);
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
l_Lean_addSearchPathFromEnv___closed__1 = _init_l_Lean_addSearchPathFromEnv___closed__1();
lean_mark_persistent(l_Lean_addSearchPathFromEnv___closed__1);
l_Lean_modPathToFilePath___main___closed__1 = _init_l_Lean_modPathToFilePath___main___closed__1();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__1);
l_Lean_modPathToFilePath___main___closed__2 = _init_l_Lean_modPathToFilePath___main___closed__2();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__2);
l_Lean_modPathToFilePath___main___closed__3 = _init_l_Lean_modPathToFilePath___main___closed__3();
lean_mark_persistent(l_Lean_modPathToFilePath___main___closed__3);
l_Lean_splitAtRoot___main___closed__1 = _init_l_Lean_splitAtRoot___main___closed__1();
lean_mark_persistent(l_Lean_splitAtRoot___main___closed__1);
l_Lean_splitAtRoot___main___closed__2 = _init_l_Lean_splitAtRoot___main___closed__2();
lean_mark_persistent(l_Lean_splitAtRoot___main___closed__2);
l_Lean_findOLean___closed__1 = _init_l_Lean_findOLean___closed__1();
lean_mark_persistent(l_Lean_findOLean___closed__1);
l_Lean_findOLean___closed__2 = _init_l_Lean_findOLean___closed__2();
lean_mark_persistent(l_Lean_findOLean___closed__2);
l_Lean_findAtSearchPath___closed__1 = _init_l_Lean_findAtSearchPath___closed__1();
lean_mark_persistent(l_Lean_findAtSearchPath___closed__1);
l_Lean_findAtSearchPath___closed__2 = _init_l_Lean_findAtSearchPath___closed__2();
lean_mark_persistent(l_Lean_findAtSearchPath___closed__2);
l_Lean_moduleNameOfFileName___closed__1 = _init_l_Lean_moduleNameOfFileName___closed__1();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__1);
l_Lean_moduleNameOfFileName___closed__2 = _init_l_Lean_moduleNameOfFileName___closed__2();
lean_mark_persistent(l_Lean_moduleNameOfFileName___closed__2);
l_Lean_normalizeModuleName___closed__1 = _init_l_Lean_normalizeModuleName___closed__1();
lean_mark_persistent(l_Lean_normalizeModuleName___closed__1);
l_Lean_normalizeModuleName___closed__2 = _init_l_Lean_normalizeModuleName___closed__2();
lean_mark_persistent(l_Lean_normalizeModuleName___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
