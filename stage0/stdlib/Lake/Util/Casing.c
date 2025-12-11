// Lean compiler output
// Module: Lake.Util.Casing
// Imports: public import Init.Data.String.Basic import Init.Data.String.Modify import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object*);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_toUpperCamelCaseString___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCaseString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_20 = x_4;
} else {
 lean_dec_ref(x_4);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_nat_sub(x_22, x_21);
x_24 = lean_nat_dec_eq(x_19, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; uint32_t x_35; uint32_t x_36; uint8_t x_37; 
x_25 = lean_string_utf8_next_fast(x_2, x_19);
x_35 = lean_string_utf8_get_fast(x_2, x_19);
x_36 = 95;
x_37 = lean_uint32_dec_eq(x_35, x_36);
if (x_37 == 0)
{
uint32_t x_38; uint8_t x_39; 
x_38 = 45;
x_39 = lean_uint32_dec_eq(x_35, x_38);
x_26 = x_39;
goto block_34;
}
else
{
x_26 = x_37;
goto block_34;
}
block_34:
{
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_19);
if (lean_is_scalar(x_20)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_20;
}
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_25);
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_1);
x_29 = l_String_Slice_slice_x21(x_1, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
if (lean_is_scalar(x_20)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_20;
}
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_25);
x_6 = x_33;
x_7 = x_30;
x_8 = x_31;
x_9 = x_32;
goto block_17;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_20);
lean_dec(x_19);
x_40 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_40;
x_7 = x_2;
x_8 = x_18;
x_9 = x_3;
goto block_17;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
block_17:
{
lean_object* x_10; lean_object* x_11; uint32_t x_12; uint32_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_get(x_10, x_11);
x_13 = l_Char_toUpper(x_12);
x_14 = lean_string_utf8_set(x_10, x_11, x_13);
x_15 = lean_array_push(x_5, x_14);
x_4 = x_6;
x_5 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(x_1, x_3, x_4, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0;
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_string_append(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lake_toUpperCamelCaseString___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
x_5 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(x_4);
x_6 = l_Lake_toUpperCamelCaseString___closed__0;
x_7 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(x_4, x_1, x_3, x_5, x_6);
x_8 = lean_array_to_list(x_7);
x_9 = l_Lake_toUpperCamelCaseString___closed__1;
x_10 = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(x_9, x_8);
lean_dec(x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_toUpperCamelCase(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = l_Lake_toUpperCamelCase(x_2);
x_5 = l_Lake_toUpperCamelCaseString(x_3);
x_6 = l_Lean_Name_str___override(x_4, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Casing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0 = _init_l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0();
lean_mark_persistent(l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___closed__0);
l_Lake_toUpperCamelCaseString___closed__0 = _init_l_Lake_toUpperCamelCaseString___closed__0();
lean_mark_persistent(l_Lake_toUpperCamelCaseString___closed__0);
l_Lake_toUpperCamelCaseString___closed__1 = _init_l_Lake_toUpperCamelCaseString___closed__1();
lean_mark_persistent(l_Lake_toUpperCamelCaseString___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
