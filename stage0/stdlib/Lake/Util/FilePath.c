// Lean compiler output
// Module: Lake.Util.FilePath
// Imports: Lean.Data.Json
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_joinRelative___closed__3;
uint8_t l_System_FilePath_isAbsolute(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_joinRelative___closed__1;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_joinRelative___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at_Lake_mkRelPathString___spec__1(lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
static lean_object* l_Lake_joinRelative___closed__2;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_instDivFilePath__lake___closed__1;
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDivFilePath__lake;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT lean_object* l_String_mapAux___at_Lake_mkRelPathString___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = 92;
x_6 = lean_uint32_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_string_utf8_set(x_2, x_1, x_4);
x_8 = lean_string_utf8_next(x_7, x_1);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
else
{
uint32_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 47;
x_11 = lean_string_utf8_set(x_2, x_1, x_10);
x_12 = lean_string_utf8_next(x_11, x_1);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_11;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_Platform_isWindows;
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___at_Lake_mkRelPathString___spec__1(x_3, x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_joinRelative___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_joinRelative___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_joinRelative___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_Lake_joinRelative___closed__2;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lake_joinRelative___closed__1;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_string_dec_eq(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_System_FilePath_isAbsolute(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lake_joinRelative___closed__3;
x_8 = lean_string_append(x_1, x_7);
x_9 = lean_string_append(x_8, x_2);
return x_9;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_joinRelative(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instDivFilePath__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_joinRelative___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDivFilePath__lake() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDivFilePath__lake___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_joinRelative(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instHDivFilePathString__lake(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_FilePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_joinRelative___closed__1 = _init_l_Lake_joinRelative___closed__1();
lean_mark_persistent(l_Lake_joinRelative___closed__1);
l_Lake_joinRelative___closed__2 = _init_l_Lake_joinRelative___closed__2();
lean_mark_persistent(l_Lake_joinRelative___closed__2);
l_Lake_joinRelative___closed__3 = _init_l_Lake_joinRelative___closed__3();
lean_mark_persistent(l_Lake_joinRelative___closed__3);
l_Lake_instDivFilePath__lake___closed__1 = _init_l_Lake_instDivFilePath__lake___closed__1();
lean_mark_persistent(l_Lake_instDivFilePath__lake___closed__1);
l_Lake_instDivFilePath__lake = _init_l_Lake_instDivFilePath__lake();
lean_mark_persistent(l_Lake_instDivFilePath__lake);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
