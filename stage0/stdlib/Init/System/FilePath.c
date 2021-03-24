// Lean compiler output
// Module: Init.System.FilePath
// Imports: Init.System.Platform Init.Data.String.Basic
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
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l_System_FilePath_exeSuffix___closed__1;
lean_object* lean_string_push(lean_object*, uint32_t);
extern uint8_t l_System_Platform_isWindows;
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__1___boxed(lean_object*);
extern uint8_t l_System_Platform_isOSX;
lean_object* l_String_revPosOf(lean_object*, uint32_t);
uint8_t l_System_FilePath_isCaseInsensitive;
lean_object* l_System_mkFilePath(lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
lean_object* l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_System_FilePath_splitSearchPath(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldr___at_System_FilePath_normalizePath___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_mapAux___at_System_FilePath_normalizePath___spec__4(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathSeparators;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_System_FilePath_normalizePath___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_System_FilePath_normalizePath___closed__1;
lean_object* l_System_FilePath_splitSearchPath___boxed(lean_object*);
lean_object* l_System_FilePath_normalizePath(lean_object*);
uint32_t l_System_FilePath_pathSeparator___closed__1;
uint32_t l_System_FilePath_pathSeparator;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t l_System_FilePath_isCaseInsensitive___closed__1;
uint32_t l_System_FilePath_searchPathSeparator___closed__1;
lean_object* l_System_FilePath_exeSuffix___closed__2;
lean_object* l_String_mapAux___at_System_FilePath_normalizePath___spec__2(lean_object*, lean_object*);
lean_object* l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_System_FilePath_extSeparator;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint32_t l_System_FilePath_searchPathSeparator;
lean_object* l_System_FilePath_pathSeparators___closed__3;
lean_object* l_System_mkFilePath___closed__1;
lean_object* l_List_foldr___at_System_FilePath_normalizePath___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__2;
uint8_t l_List_foldr___at_System_FilePath_normalizePath___spec__3(uint32_t, uint8_t, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__1;
lean_object* l_System_FilePath_parent(lean_object*);
uint8_t l_List_foldr___at_System_FilePath_normalizePath___spec__1(uint32_t, uint8_t, lean_object*);
lean_object* l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
lean_object* l_System_FilePath_exeSuffix;
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__1(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static uint32_t _init_l_System_FilePath_pathSeparator___closed__1() {
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
static uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_pathSeparator___closed__1;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_System_FilePath_pathSeparators___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators___closed__1;
x_2 = l_System_FilePath_pathSeparators___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_pathSeparators___closed__3() {
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
static lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_pathSeparators___closed__3;
return x_1;
}
}
static uint32_t _init_l_System_FilePath_searchPathSeparator___closed__1() {
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
static uint32_t _init_l_System_FilePath_searchPathSeparator() {
_start:
{
uint32_t x_1; 
x_1 = l_System_FilePath_searchPathSeparator___closed__1;
return x_1;
}
}
lean_object* l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_System_FilePath_searchPathSeparator;
x_8 = x_7 == x_6;
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_11, x_12);
x_14 = lean_string_utf8_extract(x_1, x_2, x_13);
lean_dec(x_13);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = l_List_reverse___rarg(x_18);
return x_19;
}
}
}
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
lean_object* l_System_FilePath_splitSearchPath(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_System_FilePath_splitSearchPath___spec__1(x_1);
return x_2;
}
}
lean_object* l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_System_FilePath_splitSearchPath___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_String_split___at_System_FilePath_splitSearchPath___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_System_FilePath_splitSearchPath___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_System_FilePath_splitSearchPath___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_splitSearchPath(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
uint32_t x_1; 
x_1 = 46;
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(".exe");
return x_1;
}
}
static lean_object* _init_l_System_FilePath_exeSuffix___closed__2() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_System_FilePath_exeSuffix___closed__1;
return x_3;
}
}
}
static lean_object* _init_l_System_FilePath_exeSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_System_FilePath_exeSuffix___closed__2;
return x_1;
}
}
static uint8_t _init_l_System_FilePath_isCaseInsensitive___closed__1() {
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
static uint8_t _init_l_System_FilePath_isCaseInsensitive() {
_start:
{
uint8_t x_1; 
x_1 = l_System_FilePath_isCaseInsensitive___closed__1;
return x_1;
}
}
uint8_t l_List_foldr___at_System_FilePath_normalizePath___spec__1(uint32_t x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___at_System_FilePath_normalizePath___spec__1(x_1, x_2, x_5);
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
lean_object* l_String_mapAux___at_System_FilePath_normalizePath___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_foldr___at_System_FilePath_normalizePath___spec__1(x_4, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_set(x_2, x_1, x_4);
x_9 = lean_string_utf8_next(x_8, x_1);
lean_dec(x_1);
x_1 = x_9;
x_2 = x_8;
goto _start;
}
else
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_System_FilePath_pathSeparator;
x_12 = lean_string_utf8_set(x_2, x_1, x_11);
x_13 = lean_string_utf8_next(x_12, x_1);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_12;
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
uint8_t l_List_foldr___at_System_FilePath_normalizePath___spec__3(uint32_t x_1, uint8_t x_2, lean_object* x_3) {
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
x_6 = l_List_foldr___at_System_FilePath_normalizePath___spec__3(x_1, x_2, x_5);
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
lean_object* l_String_mapAux___at_System_FilePath_normalizePath___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_foldr___at_System_FilePath_normalizePath___spec__3(x_4, x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_set(x_2, x_1, x_4);
x_9 = lean_string_utf8_next(x_8, x_1);
lean_dec(x_1);
x_1 = x_9;
x_2 = x_8;
goto _start;
}
else
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_System_FilePath_pathSeparator;
x_12 = lean_string_utf8_set(x_2, x_1, x_11);
x_13 = lean_string_utf8_next(x_12, x_1);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_12;
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
static lean_object* _init_l_System_FilePath_normalizePath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_FilePath_pathSeparators;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthAux___rarg(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_System_FilePath_normalizePath___closed__2() {
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
x_4 = l_String_mapAux___at_System_FilePath_normalizePath___spec__2(x_3, x_1);
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
x_7 = l_String_mapAux___at_System_FilePath_normalizePath___spec__4(x_6, x_1);
return x_7;
}
}
}
}
lean_object* l_List_foldr___at_System_FilePath_normalizePath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___at_System_FilePath_normalizePath___spec__1(x_4, x_5, x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_List_foldr___at_System_FilePath_normalizePath___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_foldr___at_System_FilePath_normalizePath___spec__3(x_4, x_5, x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_System_FilePath_parent(lean_object* x_1) {
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
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_extract(x_2, x_8, x_7);
lean_dec(x_7);
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_extract(x_2, x_11, x_10);
lean_dec(x_10);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_System_mkFilePath___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedParserDescr___closed__1;
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_string_push(x_1, x_2);
return x_3;
}
}
lean_object* l_System_mkFilePath(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_System_mkFilePath___closed__1;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init_System_Platform(lean_object*);
lean_object* initialize_Init_Data_String_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_System_FilePath(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Platform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_System_FilePath_exeSuffix___closed__1 = _init_l_System_FilePath_exeSuffix___closed__1();
lean_mark_persistent(l_System_FilePath_exeSuffix___closed__1);
l_System_FilePath_exeSuffix___closed__2 = _init_l_System_FilePath_exeSuffix___closed__2();
lean_mark_persistent(l_System_FilePath_exeSuffix___closed__2);
l_System_FilePath_exeSuffix = _init_l_System_FilePath_exeSuffix();
lean_mark_persistent(l_System_FilePath_exeSuffix);
l_System_FilePath_isCaseInsensitive___closed__1 = _init_l_System_FilePath_isCaseInsensitive___closed__1();
l_System_FilePath_isCaseInsensitive = _init_l_System_FilePath_isCaseInsensitive();
l_System_FilePath_normalizePath___closed__1 = _init_l_System_FilePath_normalizePath___closed__1();
lean_mark_persistent(l_System_FilePath_normalizePath___closed__1);
l_System_FilePath_normalizePath___closed__2 = _init_l_System_FilePath_normalizePath___closed__2();
l_System_mkFilePath___closed__1 = _init_l_System_mkFilePath___closed__1();
lean_mark_persistent(l_System_mkFilePath___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
