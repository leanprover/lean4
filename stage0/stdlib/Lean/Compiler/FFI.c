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
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__2;
lean_object* l_String_trim(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__5;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__3;
lean_object* lean_get_linker_flags(uint8_t);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__8;
lean_object* lean_get_leanc_extra_flags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__1;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getLeancExtraFlags___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_FFI_0__Lean_Compiler_FFI_getBuiltinLinkerFlags___boxed(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__7;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__2;
lean_object* l_List_foldl___at_Array_appendList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_FFI_getCFlags(lean_object*);
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__6;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__4;
static lean_object* l_Lean_Compiler_FFI_getCFlags___closed__3;
static lean_object* l_Lean_Compiler_FFI_getLinkerFlags___closed__4;
lean_object* l_String_splitOn(lean_object*, lean_object*);
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
x_1 = lean_mk_string_from_bytes("include", 7);
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
x_1 = lean_mk_string_from_bytes("-I", 2);
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
x_1 = lean_mk_string_from_bytes(" ", 1);
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
x_1 = lean_mk_string_from_bytes("lib", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-L", 2);
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
l_Lean_Compiler_FFI_getLinkerFlags___closed__1 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__1();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__1);
l_Lean_Compiler_FFI_getLinkerFlags___closed__2 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__2();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__2);
l_Lean_Compiler_FFI_getLinkerFlags___closed__3 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__3();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__3);
l_Lean_Compiler_FFI_getLinkerFlags___closed__4 = _init_l_Lean_Compiler_FFI_getLinkerFlags___closed__4();
lean_mark_persistent(l_Lean_Compiler_FFI_getLinkerFlags___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
