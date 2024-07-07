// Lean compiler output
// Module: Lean.Compiler.FFI
// Imports: Init.Data.Array.Basic Init.System.FilePath
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
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__7;
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__5;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
lean_object* lean_get_linker_flags(uint8_t);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__8;
lean_object* lean_get_leanc_extra_flags(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__5;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object*);
static size_t l_Lean_Compiler_FFI_getInternalCFlags___closed__8;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__4;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__7;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__6;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__6;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__4;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_get_leanc_internal_flags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4;
lean_object* l_String_splitOn(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("include", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-I", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__5;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__6;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_3 = l_String_splitOn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lean_Compiler_FFI_getCFlags___closed__4;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_7 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_internal_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ROOT", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1;
x_10 = l_String_replace(x_6, x_9, x_1);
lean_dec(x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_internal_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_3 = l_String_splitOn(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
x_2 = l_List_redLength___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__4;
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__5;
x_3 = l_List_toArrayAux___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__6;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__7;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_Lean_Compiler_FFI_getInternalCFlags___closed__8;
x_4 = l_Lean_Compiler_FFI_getInternalCFlags___closed__6;
x_5 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_FFI_getInternalCFlags(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = lean_get_linker_flags(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_2 = l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
x_6 = l_System_FilePath_join(x_4, x_5);
x_7 = l_Lean_Compiler_FFI_getLinkerFlags___closed__4;
x_8 = lean_array_push(x_7, x_6);
x_9 = lean_get_linker_flags(x_2);
x_10 = l_String_trim(x_9);
lean_dec(x_9);
x_11 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_12 = l_String_splitOn(x_10, x_11);
x_13 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_8, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lean_Compiler_FFI_getLinkerFlags(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_internal_linker_flags(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1;
x_10 = l_String_replace(x_6, x_9, x_1);
lean_dec(x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_internal_linker_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = l_String_trim(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_3 = l_String_splitOn(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
x_2 = l_List_redLength___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4;
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5;
x_3 = l_List_toArrayAux___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* x_1) {
_start:
{
size_t x_2; size_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8;
x_4 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6;
x_5 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(x_1, x_3, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_FFI(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_FFI_getCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__1);
l_Lean_Compiler_FFI_getCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getCFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__2);
l_Lean_Compiler_FFI_getCFlags___closed__3 = _init_l_Lean_Compiler_FFI_getCFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__3);
l_Lean_Compiler_FFI_getCFlags___closed__4 = _init_l_Lean_Compiler_FFI_getCFlags___closed__4();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__4);
l_Lean_Compiler_FFI_getCFlags___closed__5 = _init_l_Lean_Compiler_FFI_getCFlags___closed__5();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__5);
l_Lean_Compiler_FFI_getCFlags___closed__6 = _init_l_Lean_Compiler_FFI_getCFlags___closed__6();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__6);
l_Lean_Compiler_FFI_getCFlags___closed__7 = _init_l_Lean_Compiler_FFI_getCFlags___closed__7();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__7);
l_Lean_Compiler_FFI_getCFlags___closed__8 = _init_l_Lean_Compiler_FFI_getCFlags___closed__8();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__8);
l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___closed__1);
l_Lean_Compiler_FFI_getInternalCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
l_Lean_Compiler_FFI_getInternalCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__2);
l_Lean_Compiler_FFI_getInternalCFlags___closed__3 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__3);
l_Lean_Compiler_FFI_getInternalCFlags___closed__4 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__4();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__4);
l_Lean_Compiler_FFI_getInternalCFlags___closed__5 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__5();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__5);
l_Lean_Compiler_FFI_getInternalCFlags___closed__6 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__6();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__6);
l_Lean_Compiler_FFI_getInternalCFlags___closed__7 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__7();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__7);
l_Lean_Compiler_FFI_getInternalCFlags___closed__8 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__8();
l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__2);
l_Lean_Compiler_FFI_getLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
l_Lean_Compiler_FFI_getLinkerFlags___closed__4 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__4();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__4);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
