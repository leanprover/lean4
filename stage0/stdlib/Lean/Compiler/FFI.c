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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
lean_object* lean_get_linker_flags(uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_get_leanc_extra_flags(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags___boxed(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0;
static size_t l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancInternalFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
static lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0;
static size_t l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinInternalLinkerFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__0;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
lean_object* l_String_replace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
lean_object* lean_get_internal_linker_flags(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__0;
static lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_get_leanc_internal_flags(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
static uint8_t l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags_x27;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
x_13 = lean_string_dec_eq(x_11, x_12);
x_14 = l_instDecidableNot___redArg(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_15; 
x_15 = lean_array_push(x_4, x_11);
x_5 = x_15;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_13; uint8_t x_14; 
x_13 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1;
x_14 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__2;
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = l_String_splitOnAux(x_1, x_13, x_15, x_15, x_15, x_16);
lean_dec(x_1);
x_2 = x_17;
goto block_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
goto block_12;
}
block_12:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_array_mk(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0;
x_7 = lean_nat_dec_lt(x_4, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_3, x_9, x_10, x_6);
lean_dec(x_3);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_extra_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getCFlags_x27___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags_x27() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_FFI_getCFlags_x27___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getCFlags___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-I", 2, 2);
return x_1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getCFlags___closed__0;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__1;
x_3 = l_System_FilePath_join(x_1, x_2);
x_4 = l_Lean_Compiler_FFI_getCFlags___closed__3;
x_5 = lean_array_push(x_4, x_3);
x_6 = l_Lean_Compiler_FFI_getCFlags_x27;
x_7 = l_Array_append___redArg(x_5, x_6);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ROOT", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0;
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
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_leanc_internal_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalCFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_FFI_getInternalCFlags___closed__1;
x_3 = l_Lean_Compiler_FFI_getInternalCFlags___closed__2;
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0(x_1, x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0(x_1, x_5, x_6, x_4);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_get_linker_flags(x_1);
x_3 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags_x27___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-L", 2, 2);
return x_1;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_FFI_getLinkerFlags___closed__0;
x_2 = l_Lean_Compiler_FFI_getCFlags___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getLinkerFlags(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
x_4 = l_System_FilePath_join(x_1, x_3);
x_5 = l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
x_6 = l_System_FilePath_join(x_4, x_5);
x_7 = l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Lean_Compiler_FFI_getLinkerFlags_x27(x_2);
x_10 = l_Array_append___redArg(x_8, x_9);
lean_dec(x_9);
return x_10;
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
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_get_internal_linker_flags(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0;
x_2 = l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_2 = lean_array_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getInternalLinkerFlags(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1;
x_3 = l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2;
x_4 = 0;
x_5 = l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0(x_1, x_3, x_4, x_2);
return x_5;
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
l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0 = _init_l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_____private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray_spec__0___closed__0);
l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0 = _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__0);
l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1 = _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__1);
l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__2 = _init_l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_flagsStringToArray___closed__2();
l_Lean_Compiler_FFI_getCFlags_x27___closed__0 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__0);
l_Lean_Compiler_FFI_getCFlags_x27___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags_x27___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27___closed__1);
l_Lean_Compiler_FFI_getCFlags_x27 = _init_l_Lean_Compiler_FFI_getCFlags_x27();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags_x27);
l_Lean_Compiler_FFI_getCFlags___closed__0 = _init_l_Lean_Compiler_FFI_getCFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__0);
l_Lean_Compiler_FFI_getCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__1);
l_Lean_Compiler_FFI_getCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getCFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__2);
l_Lean_Compiler_FFI_getCFlags___closed__3 = _init_l_Lean_Compiler_FFI_getCFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getCFlags___closed__3);
l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0 = _init_l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___Lean_Compiler_FFI_getInternalCFlags_spec__0___closed__0);
l_Lean_Compiler_FFI_getInternalCFlags___closed__0 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__0);
l_Lean_Compiler_FFI_getInternalCFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalCFlags___closed__1);
l_Lean_Compiler_FFI_getInternalCFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalCFlags___closed__2();
l_Lean_Compiler_FFI_getLinkerFlags___closed__0 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__0);
l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__2);
l_Lean_Compiler_FFI_getLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__0);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getInternalLinkerFlags___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
