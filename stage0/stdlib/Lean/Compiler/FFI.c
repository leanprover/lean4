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
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__7;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__5;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
lean_object* lean_get_linker_flags(uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__8;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_get_leanc_extra_flags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__12;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__5;
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__10;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__9;
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
static uint8_t l_Lean_Compiler_FFI_getCFlags___closed__10;
lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
static size_t l_Lean_Compiler_FFI_getInternalCFlags___closed__11;
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__4;
lean_object* l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__7;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__11;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__6;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__6;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__11;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__4;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_get_leanc_internal_flags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2(lean_object*, size_t, size_t, lean_object*);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-I", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__4;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__5;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__4;
x_4 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__5;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__6;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l_Lean_Compiler_FFI_getCFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__9;
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_splitOnAux(x_2, x_3, x_4, x_4, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_array_mk(x_7);
x_9 = l_Lean_Compiler_FFI_getCFlags___closed__10;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Compiler_FFI_getCFlags___closed__11;
x_11 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_8, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Compiler_FFI_getCFlags___closed__12;
x_13 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_8, x_12);
return x_13;
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
x_3 = l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
x_4 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__3;
x_3 = l_Lean_Compiler_FFI_getInternalCFlags___closed__4;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__5;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_splitOnAux(x_2, x_3, x_4, x_4, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__7;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__9;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__11() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__10;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__10;
if (x_3 == 0)
{
size_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_FFI_getInternalCFlags___closed__8;
x_5 = l_Lean_Compiler_FFI_getInternalCFlags___closed__7;
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__1(x_1, x_4, x_2, x_5);
return x_6;
}
else
{
size_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Compiler_FFI_getInternalCFlags___closed__11;
x_8 = l_Lean_Compiler_FFI_getInternalCFlags___closed__10;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2(x_1, x_7, x_2, x_8);
return x_9;
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalCFlags___spec__2(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_3 = l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
x_6 = l_System_FilePath_join(x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_array_mk(x_10);
x_12 = lean_get_linker_flags(x_2);
x_13 = lean_string_utf8_byte_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_12, x_13, x_14);
x_16 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_12, x_15, x_13);
x_17 = lean_string_utf8_extract(x_12, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_18 = l_Lean_Compiler_FFI_getCFlags___closed__10;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_20 = l_String_splitOnAux(x_17, x_19, x_14, x_14, x_14, x_7);
lean_dec(x_17);
x_21 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_11, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_7);
x_23 = l_List_foldl___at_Array_appendList___spec__1___rarg(x_11, x_22);
return x_23;
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Substring_takeWhileAux___at_Substring_trimLeft___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
x_3 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
x_4 = l_Substring_takeRightWhileAux___at_Substring_trimRight___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__3;
x_3 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__4;
x_4 = lean_string_utf8_extract(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__8;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_splitOnAux(x_2, x_3, x_4, x_4, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__6;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7;
x_2 = lean_array_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__11() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* x_1) {
_start:
{
size_t x_2; uint8_t x_3; 
x_2 = 0;
x_3 = l_Lean_Compiler_FFI_getCFlags___closed__10;
if (x_3 == 0)
{
size_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__8;
x_5 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__7;
x_6 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__1(x_1, x_4, x_2, x_5);
return x_6;
}
else
{
size_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__11;
x_8 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10;
x_9 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2(x_1, x_7, x_2, x_8);
return x_9;
}
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Compiler_FFI_getInternalLinkerFlags___spec__2(x_1, x_5, x_6, x_4);
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
l_Lean_Compiler_FFI_getCFlags___closed__9 = _init_l_Lean_Compiler_FFI_getCFlags___closed__9();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__9);
l_Lean_Compiler_FFI_getCFlags___closed__10 = _init_l_Lean_Compiler_FFI_getCFlags___closed__10();
l_Lean_Compiler_FFI_getCFlags___closed__11 = _init_l_Lean_Compiler_FFI_getCFlags___closed__11();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__11);
l_Lean_Compiler_FFI_getCFlags___closed__12 = _init_l_Lean_Compiler_FFI_getCFlags___closed__12();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__12);
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
l_Lean_Compiler_FFI_getInternalCFlags___closed__9 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__9();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__9);
l_Lean_Compiler_FFI_getInternalCFlags___closed__10 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__10();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__10);
l_Lean_Compiler_FFI_getInternalCFlags___closed__11 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__11();
l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__2);
l_Lean_Compiler_FFI_getLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
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
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__9);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__10);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__11 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__11();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
