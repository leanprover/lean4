// Lean compiler output
// Module: init.system.filepath
// Imports: init.system.platform init.data.string.basic
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
lean_object* l_String_revPosOf(lean_object*, uint32_t);
uint32_t l_System_FilePath_pathSeparator___closed__1;
lean_object* l_List_foldr___main___at_System_FilePath_normalizePath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__3;
extern uint8_t l_System_Platform_isWindows;
lean_object* l_System_FilePath_normalizePath(lean_object*);
uint8_t l_System_FilePath_isCaseInsensitive;
lean_object* l_System_FilePath_pathSeparators___closed__2;
uint32_t l_System_FilePath_searchPathSeparator;
lean_object* l_System_FilePath_pathSeparators;
lean_object* l_System_FilePath_pathSeparators___closed__1;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_System_FilePath_dirName(lean_object*);
uint8_t l_System_FilePath_isCaseInsensitive___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t l_System_FilePath_searchPathSeparator___closed__1;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
extern uint8_t l_System_Platform_isOSX;
lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
uint32_t l_System_FilePath_extSeparator;
uint32_t l_System_FilePath_pathSeparator;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
uint32_t l_Char_toLower(uint32_t);
uint8_t l_System_FilePath_normalizePath___closed__2;
lean_object* l_System_FilePath_normalizePath___closed__1;
uint8_t l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(uint32_t, uint8_t, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t _init_l_System_FilePath_pathSeparator___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 47;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 92;
return x_3;
}
}
}
uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
return x_1;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 47;
x_2 = lean_box(0);
x_3 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 92;
x_2 = l_System_FilePath_pathSeparators___closed__1;
x_3 = l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
lean_object* _init_l_System_FilePath_pathSeparators___closed__3() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_System_FilePath_pathSeparators___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_pathSeparators___closed__2;
return x_3;
}
}
}
lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
uint32_t _init_l_System_FilePath_searchPathSeparator___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint32_t x_2; 
x_2 = 58;
return x_2;
}
else
{
uint32_t x_3; 
x_3 = 59;
return x_3;
}
}
}
uint32_t _init_l_System_FilePath_searchPathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_searchPathSeparator___closed__1;
return x_1;
}
}
uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
uint8_t _init_l_System_FilePath_isCaseInsensitive___closed__1() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l_System_Platform_isOSX;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
uint8_t _init_l_System_FilePath_isCaseInsensitive() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_isCaseInsensitive___closed__1;
return x_1;
}
}
uint8_t l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(uint32_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint32_t x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_1, x_2, x_5);
x_7 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_8 = x_1 == x_7;
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = 0;
x_6 = l_System_FilePath_pathSeparators;
x_7 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_4, x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_System_FilePath_isCaseInsensitive;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_string_utf8_set(x_2, x_1, x_4);
x_10 = lean_string_utf8_next(x_9, x_1);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_9;
goto _start;
}
else
{
uint32_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Char_toLower(x_4);
x_13 = lean_string_utf8_set(x_2, x_1, x_12);
x_14 = lean_string_utf8_next(x_13, x_1);
lean_dec(x_1);
x_1 = x_14;
x_2 = x_13;
goto _start;
}
}
else
{
uint32_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_System_FilePath_pathSeparator;
x_17 = lean_string_utf8_set(x_2, x_1, x_16);
x_18 = lean_string_utf8_next(x_17, x_1);
lean_dec(x_1);
x_1 = x_18;
x_2 = x_17;
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
lean_object* _init_l_System_FilePath_normalizePath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthAux___main___rarg(x_1, x_2);
return x_3;
}
}
uint8_t _init_l_System_FilePath_normalizePath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_System_FilePath_normalizePath___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_System_FilePath_normalizePath(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_FilePath_normalizePath___closed__2;
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(x_3, x_1);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_System_FilePath_isCaseInsensitive;
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_mapAux___main___at_System_FilePath_normalizePath___spec__2(x_6, x_1);
return x_7;
}
}
}
}
lean_object* l_List_foldr___main___at_System_FilePath_normalizePath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___main___at_System_FilePath_normalizePath___spec__1(x_4, x_5, x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l_System_FilePath_dirName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".");
return x_1;
}
}
lean_object* l_System_FilePath_dirName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_2 = l_System_FilePath_normalizePath(x_1);
x_3 = l_System_FilePath_pathSeparator;
x_4 = l_String_revPosOf(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_System_FilePath_dirName___closed__1;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_extract(x_2, x_7, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
}
lean_object* initialize_init_system_platform(lean_object*);
lean_object* initialize_init_data_string_basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_system_filepath(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_system_platform(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_data_string_basic(w);
if (lean_io_result_is_error(w)) return w;
l_System_FilePath_pathSeparator___closed__1 = _init_l_System_FilePath_pathSeparator___closed__1();
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators___closed__1___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1___boxed__const__1);
l_System_FilePath_pathSeparators___closed__1 = _init_l_System_FilePath_pathSeparators___closed__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__1);
l_System_FilePath_pathSeparators___closed__2___boxed__const__1 = _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2___boxed__const__1);
l_System_FilePath_pathSeparators___closed__2 = _init_l_System_FilePath_pathSeparators___closed__2();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__2);
l_System_FilePath_pathSeparators___closed__3 = _init_l_System_FilePath_pathSeparators___closed__3();
lean_mark_persistent(l_System_FilePath_pathSeparators___closed__3);
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_searchPathSeparator___closed__1 = _init_l_System_FilePath_searchPathSeparator___closed__1();
l_System_FilePath_searchPathSeparator = _init_l_System_FilePath_searchPathSeparator();
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_isCaseInsensitive___closed__1 = _init_l_System_FilePath_isCaseInsensitive___closed__1();
l_System_FilePath_isCaseInsensitive = _init_l_System_FilePath_isCaseInsensitive();
l_System_FilePath_normalizePath___closed__1 = _init_l_System_FilePath_normalizePath___closed__1();
lean_mark_persistent(l_System_FilePath_normalizePath___closed__1);
l_System_FilePath_normalizePath___closed__2 = _init_l_System_FilePath_normalizePath___closed__2();
l_System_FilePath_dirName___closed__1 = _init_l_System_FilePath_dirName___closed__1();
lean_mark_persistent(l_System_FilePath_dirName___closed__1);
return w;
}
#ifdef __cplusplus
}
#endif
