// Lean compiler output
// Module: Lake.Util.Casing
// Imports: Init
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
static lean_object* l_Lake_toUpperCamelCaseString___closed__1;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString___boxed(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase___boxed(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_String_join___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_Lake_toUpperCamelCaseString___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_split___at_Lake_toUpperCamelCaseString___spec__1(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_toUpperCamelCaseString___spec__3(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object*);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = 95;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 45;
x_10 = lean_uint32_dec_eq(x_6, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_string_utf8_next(x_1, x_3);
x_14 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
lean_inc(x_13);
x_2 = x_13;
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_string_utf8_next(x_1, x_3);
x_18 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
lean_inc(x_17);
x_2 = x_17;
x_3 = x_17;
x_4 = x_19;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
x_23 = l_List_reverse___rarg(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lake_toUpperCamelCaseString___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2(x_1, x_3, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lake_toUpperCamelCaseString___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_string_utf8_get(x_5, x_7);
x_9 = l_Char_toUpper(x_8);
x_10 = lean_unbox_uint32(x_9);
lean_dec(x_9);
x_11 = lean_string_utf8_set(x_5, x_7, x_10);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_utf8_get(x_13, x_15);
x_17 = l_Char_toUpper(x_16);
x_18 = lean_unbox_uint32(x_17);
lean_dec(x_17);
x_19 = lean_string_utf8_set(x_13, x_15, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_toUpperCamelCaseString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_String_split___at_Lake_toUpperCamelCaseString___spec__1(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at_Lake_toUpperCamelCaseString___spec__3(x_2, x_3);
x_5 = l_Lake_toUpperCamelCaseString___closed__1;
x_6 = l_List_foldl___at_String_join___spec__1(x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at_Lake_toUpperCamelCaseString___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at_Lake_toUpperCamelCaseString___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at_Lake_toUpperCamelCaseString___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_toUpperCamelCaseString(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lake_toUpperCamelCase(x_2);
x_5 = l_Lake_toUpperCamelCaseString(x_3);
x_6 = l_Lean_Name_str___override(x_4, x_5);
return x_6;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_toUpperCamelCase(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Casing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_toUpperCamelCaseString___closed__1 = _init_l_Lake_toUpperCamelCaseString___closed__1();
lean_mark_persistent(l_Lake_toUpperCamelCaseString___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
