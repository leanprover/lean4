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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_String_stripSuffix(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake;
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___lam__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake;
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object*, lean_object*);
lean_object* l_String_dropPrefix_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modOfFilePath_removeExts(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_mkRelPathString_spec__0(lean_object*, lean_object*);
lean_object* l_System_FilePath_components(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modOfFilePath_removeExts___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_joinRelative___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_modOfFilePath_spec__0(lean_object*, lean_object*);
extern uint32_t l_System_FilePath_pathSeparator;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_modOfFilePath___closed__0;
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkRelPathString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDivFilePath__lake;
static lean_object* l_Lake_joinRelative___closed__0;
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lake_instDivFilePath__lake___closed__0;
extern uint8_t l_System_Platform_isWindows;
static lean_object* l_Lake_modOfFilePath___closed__1;
LEAN_EXPORT lean_object* l_Lake_relPathFrom(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_String_dropPrefix_x3f(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Substring_nextn(x_4, x_8, x_9);
lean_dec(x_4);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_12 = lean_string_utf8_extract(x_5, x_11, x_7);
lean_dec(x_7);
lean_dec(x_11);
lean_dec(x_5);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_mkRelPathString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_2, x_1);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get(x_2, x_1);
x_10 = 92;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_3 = x_9;
goto block_7;
}
else
{
uint32_t x_12; 
x_12 = 47;
x_3 = x_12;
goto block_7;
}
}
else
{
lean_dec(x_1);
return x_2;
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_set(x_2, x_1, x_3);
x_5 = lean_string_utf8_next(x_4, x_1);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
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
x_4 = l_String_mapAux___at___Lake_mkRelPathString_spec__0(x_3, x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonFilePath__lake___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_mkRelPathString(x_1);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToJsonFilePath__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instToJsonFilePath__lake___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_joinRelative___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_joinRelative(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lake_joinRelative___closed__0;
x_4 = lean_string_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_string_dec_eq(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_System_FilePath_join(x_1, x_2);
return x_6;
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
static lean_object* _init_l_Lake_instDivFilePath__lake___closed__0() {
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
x_1 = l_Lake_instDivFilePath__lake___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_joinRelative(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHDivFilePathString__lake() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instHDivFilePathString__lake___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instHDivFilePathString__lake___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instHDivFilePathString__lake___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath_removeExts(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_prev(x_1, x_2);
lean_dec(x_2);
x_7 = lean_string_utf8_get(x_1, x_6);
x_8 = l_System_FilePath_pathSeparator;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 46;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_3);
lean_inc(x_6);
x_2 = x_6;
x_3 = x_6;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = lean_string_utf8_extract(x_1, x_4, x_3);
lean_dec(x_3);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_string_utf8_extract(x_1, x_4, x_3);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath_removeExts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_modOfFilePath_removeExts(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lake_modOfFilePath_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Lean_Name_str___override(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lake_modOfFilePath___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_modOfFilePath___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparator;
x_2 = l_Lake_modOfFilePath___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_modOfFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = lean_string_utf8_byte_size(x_2);
lean_inc(x_3);
x_4 = l_Lake_modOfFilePath_removeExts(x_2, x_3, x_3);
lean_dec(x_2);
x_5 = l_Lake_modOfFilePath___closed__1;
x_6 = l_String_stripSuffix(x_4, x_5);
x_7 = lean_box(0);
x_8 = l_System_FilePath_components(x_6);
x_9 = l_List_foldl___at___Lake_modOfFilePath_spec__0(x_7, x_8);
return x_9;
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
l_Lake_instToJsonFilePath__lake = _init_l_Lake_instToJsonFilePath__lake();
lean_mark_persistent(l_Lake_instToJsonFilePath__lake);
l_Lake_joinRelative___closed__0 = _init_l_Lake_joinRelative___closed__0();
lean_mark_persistent(l_Lake_joinRelative___closed__0);
l_Lake_instDivFilePath__lake___closed__0 = _init_l_Lake_instDivFilePath__lake___closed__0();
lean_mark_persistent(l_Lake_instDivFilePath__lake___closed__0);
l_Lake_instDivFilePath__lake = _init_l_Lake_instDivFilePath__lake();
lean_mark_persistent(l_Lake_instDivFilePath__lake);
l_Lake_instHDivFilePathString__lake = _init_l_Lake_instHDivFilePathString__lake();
lean_mark_persistent(l_Lake_instHDivFilePathString__lake);
l_Lake_modOfFilePath___closed__0 = _init_l_Lake_modOfFilePath___closed__0();
lean_mark_persistent(l_Lake_modOfFilePath___closed__0);
l_Lake_modOfFilePath___closed__1 = _init_l_Lake_modOfFilePath___closed__1();
lean_mark_persistent(l_Lake_modOfFilePath___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
