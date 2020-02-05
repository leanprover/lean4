// Lean compiler output
// Module: Init.Lean.Util.Path
// Imports: Init.System.IO Init.System.FilePath Init.Data.Array Init.Data.List.Control Init.Data.HashMap Init.Data.Nat.Control Init.Lean.Data.Name
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
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2;
lean_object* l_IO_isDir___at_Lean_parseSearchPath___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1;
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_String_revPosOf(lean_object*, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4;
lean_object* l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_searchPathRef;
lean_object* l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath(lean_object*);
lean_object* l_Lean_mkSearchPathRef(lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_modPathToFilePath___main___closed__2;
lean_object* l_Lean_findOLean(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath___main___closed__1;
lean_object* l_Lean_modPathToFilePath___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_findAtSearchPath(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_findAtSearchPath___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__1;
lean_object* l_Lean_addSearchPathFromEnv___closed__1;
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*, lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__2;
lean_object* l_System_FilePath_dirName(lean_object*);
lean_object* l_Lean_moduleNameOfFileName___closed__1;
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_System_FilePath_normalizePath(lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__5;
uint8_t l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_findOLean___closed__2;
lean_object* l_Lean_modPathToFilePath___boxed(lean_object*);
lean_object* l_Lean_modPathToFilePath___main___boxed(lean_object*);
lean_object* l_Lean_normalizeModuleName___closed__2;
extern uint32_t l_System_FilePath_pathSeparator;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_module_name_of_file(lean_object*, lean_object*);
lean_object* l_IO_appDir___at_Lean_getBuiltinSearchPath___spec__1(lean_object*);
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__2(lean_object*);
lean_object* l___private_Init_Lean_Util_Path_1__pathSep;
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__1;
lean_object* l_Lean_realPathNormalized(lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_findAtSearchPath___closed__2;
lean_object* l_IO_getEnv___at_Lean_addSearchPathFromEnv___spec__1(lean_object*, lean_object*);
lean_object* lean_init_search_path(lean_object*, lean_object*);
lean_object* l_Lean_splitAtRoot(lean_object*);
lean_object* l_Lean_findOLean___closed__1;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_findAtSearchPath___spec__3(lean_object*);
lean_object* l_Lean_normalizeModuleName___closed__1;
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_parseSearchPath___spec__4(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_addSearchPathFromEnv(lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getBuiltinSearchPath___closed__2;
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3;
lean_object* l_Lean_getBuiltinSearchPath___closed__4;
extern lean_object* l_System_mkFilePath___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_mkSearchPathRef___closed__1;
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5;
lean_object* l_mkHashMap___at_Lean_mkSearchPathRef___spec__1(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_findOLean___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_parseSearchPath(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_appPath___at_Lean_getBuiltinSearchPath___spec__2(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_findAtSearchPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modPathToFilePath(lean_object*);
lean_object* lean_io_app_dir(lean_object*);
lean_object* l_Lean_splitAtRoot___main___closed__1;
lean_object* l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__5(lean_object*, lean_object*, lean_object*);
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
lean_object* l_IO_isDir___at_Lean_parseSearchPath___spec__1(lean_object*, lean_object*);
lean_object* _init_l___private_Init_Lean_Util_Path_1__pathSep() {
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
lean_object* l_IO_isDir___at_Lean_parseSearchPath___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_is_dir(x_1, x_2);
return x_3;
}
}
uint8_t l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_parseSearchPath___spec__6(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_parseSearchPath___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_parseSearchPath___spec__5(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(x_1, x_2, x_7);
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
x_14 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_string_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_parseSearchPath___spec__4(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = lean_string_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_parseSearchPath___spec__4(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_parseSearchPath___spec__7(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed search path entry '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', should be of form 'pkg=path'");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("=");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid search path, '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a directory");
return x_1;
}
}
lean_object* l_List_foldlM___main___at_Lean_parseSearchPath___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_15 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3;
lean_inc(x_5);
x_16 = l_String_splitOn(x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_box(0);
x_7 = x_17;
goto block_14;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_box(0);
x_7 = x_19;
goto block_14;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_io_is_dir(x_22, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4;
x_29 = lean_string_append(x_28, x_22);
lean_dec(x_22);
x_30 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4;
x_35 = lean_string_append(x_34, x_22);
lean_dec(x_22);
x_36 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_dec(x_23);
x_41 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(x_1, x_21, x_22);
x_1 = x_41;
x_2 = x_6;
x_3 = x_40;
goto _start;
}
}
else
{
uint8_t x_43; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_box(0);
x_7 = x_47;
goto block_14;
}
}
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
x_8 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1;
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
x_10 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
}
lean_object* l_Lean_parseSearchPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_String_split___at_System_FilePath_splitSearchPath___spec__2(x_1);
x_5 = l_List_foldlM___main___at_Lean_parseSearchPath___spec__8(x_2, x_4, x_3);
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
lean_object* l_IO_isDir___at_Lean_parseSearchPath___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_isDir___at_Lean_parseSearchPath___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_parseSearchPath___spec__3(x_1, x_2);
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
x_5 = l___private_Init_Lean_Util_Path_1__pathSep;
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
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_getBuiltinSearchPath___closed__4;
x_20 = lean_string_append(x_9, x_19);
x_21 = lean_string_append(x_20, x_5);
x_22 = l_Lean_getBuiltinSearchPath___closed__5;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_string_append(x_23, x_5);
x_25 = lean_string_append(x_24, x_13);
x_26 = lean_io_is_dir(x_25, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_25);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = l_HashMap_Inhabited___closed__1;
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l_HashMap_Inhabited___closed__1;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_realPathNormalized(x_25, x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l_HashMap_Inhabited___closed__1;
x_40 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(x_39, x_13, x_38);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = l_HashMap_Inhabited___closed__1;
x_44 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(x_43, x_13, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_25);
x_50 = !lean_is_exclusive(x_26);
if (x_50 == 0)
{
return x_26;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_26, 0);
x_52 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_dec(x_15);
x_55 = l_Lean_realPathNormalized(x_14, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = l_HashMap_Inhabited___closed__1;
x_59 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(x_58, x_13, x_57);
lean_ctor_set(x_55, 0, x_59);
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = l_HashMap_Inhabited___closed__1;
x_63 = l_HashMapImp_insert___at_Lean_parseSearchPath___spec__2(x_62, x_13, x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_9);
x_69 = !lean_is_exclusive(x_15);
if (x_69 == 0)
{
return x_15;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_15, 0);
x_71 = lean_ctor_get(x_15, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_15);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_2);
if (x_73 == 0)
{
return x_2;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_2, 0);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_2);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
x_1 = lean_mk_string("Init.Lean.Util.Path");
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
x_2 = lean_unsigned_to_nat(84u);
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
x_7 = l___private_Init_Lean_Util_Path_1__pathSep;
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
x_14 = lean_panic_fn(x_12, x_13);
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
x_2 = lean_unsigned_to_nat(92u);
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
x_18 = lean_panic_fn(x_16, x_17);
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
lean_object* l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_string_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_findOLean___spec__2(x_2, x_7);
lean_dec(x_7);
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
x_10 = l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1(x_6, x_8);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_11 = l_Lean_findOLean___closed__1;
x_12 = lean_string_append(x_11, x_8);
lean_dec(x_8);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l___private_Init_Lean_Util_Path_1__pathSep;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Lean_modPathToFilePath___main(x_9);
lean_dec(x_9);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Lean_findOLean___closed__2;
x_22 = lean_string_append(x_20, x_21);
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = l_Lean_splitAtRoot___main(x_1);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1(x_23, x_26);
lean_dec(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_29 = l_Lean_findOLean___closed__1;
x_30 = lean_string_append(x_29, x_26);
lean_dec(x_26);
x_31 = l_Char_HasRepr___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_26);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = l___private_Init_Lean_Util_Path_1__pathSep;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_Lean_modPathToFilePath___main(x_27);
lean_dec(x_27);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = l_Lean_findOLean___closed__2;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_24);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_4);
if (x_43 == 0)
{
return x_4;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
lean_object* l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_findOLean___spec__1(x_1, x_2);
lean_dec(x_2);
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_String_isPrefixOf(x_10, x_1);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
x_3 = x_8;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_2 = x_15;
x_3 = x_8;
x_4 = x_11;
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
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
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_40);
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_dec(x_13);
x_42 = l_Lean_findAtSearchPath___closed__1;
x_43 = lean_string_append(x_42, x_4);
lean_dec(x_4);
x_44 = l_Lean_findAtSearchPath___closed__2;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_List_map___main___at_Lean_findAtSearchPath___spec__3(x_14);
x_47 = l_List_reprAux___main___rarg___closed__1;
x_48 = l_String_intercalate(x_47, x_46);
x_49 = lean_string_append(x_45, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_41);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_7);
if (x_56 == 0)
{
return x_7;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_7, 0);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_7);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
return x_3;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_3, 0);
x_62 = lean_ctor_get(x_3, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_3);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint32_t x_22; uint32_t x_23; uint8_t x_24; uint32_t x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_string_length(x_14);
lean_dec(x_14);
x_20 = l_String_drop(x_16, x_19);
lean_dec(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_get(x_20, x_21);
x_23 = l_System_FilePath_pathSeparator;
x_24 = x_22 == x_23;
x_25 = 46;
if (x_24 == 0)
{
uint8_t x_80; 
x_80 = 0;
x_26 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = 1;
x_26 = x_81;
goto block_79;
}
block_79:
{
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_String_revPosOf(x_20, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_13);
x_28 = l_Lean_moduleNameOfFileName___closed__1;
x_29 = lean_string_append(x_28, x_16);
lean_dec(x_16);
x_30 = l_Lean_moduleNameOfFileName___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_32, 0, x_31);
if (lean_is_scalar(x_18)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_18;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_string_utf8_extract(x_20, x_21, x_35);
lean_dec(x_35);
lean_dec(x_20);
x_37 = l___private_Init_Lean_Util_Path_1__pathSep;
x_38 = l_String_splitOn(x_36, x_37);
x_39 = lean_box(0);
x_40 = lean_name_mk_string(x_39, x_13);
x_41 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_40, x_38);
lean_ctor_set(x_27, 0, x_41);
if (lean_is_scalar(x_18)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_18;
}
lean_ctor_set(x_42, 0, x_27);
lean_ctor_set(x_42, 1, x_17);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_27, 0);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_string_utf8_extract(x_20, x_21, x_43);
lean_dec(x_43);
lean_dec(x_20);
x_45 = l___private_Init_Lean_Util_Path_1__pathSep;
x_46 = l_String_splitOn(x_44, x_45);
x_47 = lean_box(0);
x_48 = lean_name_mk_string(x_47, x_13);
x_49 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_48, x_46);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_18)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_18;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_17);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = l_String_drop(x_20, x_52);
lean_dec(x_20);
x_54 = l_String_revPosOf(x_53, x_25);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_53);
lean_dec(x_13);
x_55 = l_Lean_moduleNameOfFileName___closed__1;
x_56 = lean_string_append(x_55, x_16);
lean_dec(x_16);
x_57 = l_Lean_moduleNameOfFileName___closed__2;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_18)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_18;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_17);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_16);
x_61 = !lean_is_exclusive(x_54);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_string_utf8_extract(x_53, x_21, x_62);
lean_dec(x_62);
lean_dec(x_53);
x_64 = l___private_Init_Lean_Util_Path_1__pathSep;
x_65 = l_String_splitOn(x_63, x_64);
x_66 = lean_box(0);
x_67 = lean_name_mk_string(x_66, x_13);
x_68 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_67, x_65);
lean_ctor_set(x_54, 0, x_68);
if (lean_is_scalar(x_18)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_18;
}
lean_ctor_set(x_69, 0, x_54);
lean_ctor_set(x_69, 1, x_17);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
lean_dec(x_54);
x_71 = lean_string_utf8_extract(x_53, x_21, x_70);
lean_dec(x_70);
lean_dec(x_53);
x_72 = l___private_Init_Lean_Util_Path_1__pathSep;
x_73 = l_String_splitOn(x_71, x_72);
x_74 = lean_box(0);
x_75 = lean_name_mk_string(x_74, x_13);
x_76 = l_List_foldl___main___at_Lean_moduleNameOfFileName___spec__1(x_75, x_73);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
if (lean_is_scalar(x_18)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_18;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_17);
return x_78;
}
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_14);
lean_dec(x_13);
x_82 = !lean_is_exclusive(x_15);
if (x_82 == 0)
{
return x_15;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_15, 0);
x_84 = lean_ctor_get(x_15, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_15);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_3);
if (x_86 == 0)
{
return x_3;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_3, 0);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_3);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
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
lean_object* initialize_Init_Data_HashMap(lean_object*);
lean_object* initialize_Init_Data_Nat_Control(lean_object*);
lean_object* initialize_Init_Lean_Data_Name(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_Path(lean_object* w) {
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
res = initialize_Init_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Util_Path_1__pathSep = _init_l___private_Init_Lean_Util_Path_1__pathSep();
lean_mark_persistent(l___private_Init_Lean_Util_Path_1__pathSep);
l_Lean_mkSearchPathRef___closed__1 = _init_l_Lean_mkSearchPathRef___closed__1();
lean_mark_persistent(l_Lean_mkSearchPathRef___closed__1);
res = l_Lean_mkSearchPathRef(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_searchPathRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_searchPathRef);
lean_dec_ref(res);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__1);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__2);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__3);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__4);
l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5 = _init_l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5();
lean_mark_persistent(l_List_foldlM___main___at_Lean_parseSearchPath___spec__8___closed__5);
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
