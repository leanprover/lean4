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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_toUpperCamelCaseString_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_30 = x_4;
} else {
 lean_dec_ref(x_4);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_nat_sub(x_32, x_31);
x_34 = lean_nat_dec_eq(x_29, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; uint32_t x_45; uint32_t x_46; uint8_t x_47; 
x_35 = lean_string_utf8_next_fast(x_2, x_29);
x_45 = lean_string_utf8_get_fast(x_2, x_29);
x_46 = 95;
x_47 = lean_uint32_dec_eq(x_45, x_46);
if (x_47 == 0)
{
uint32_t x_48; uint8_t x_49; 
x_48 = 45;
x_49 = lean_uint32_dec_eq(x_45, x_48);
x_36 = x_49;
goto block_44;
}
else
{
x_36 = x_47;
goto block_44;
}
block_44:
{
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_29);
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_35);
x_4 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc_ref(x_1);
x_39 = l_String_Slice_slice_x21(x_1, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
if (lean_is_scalar(x_30)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_30;
}
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_35);
x_41 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 2);
lean_inc(x_43);
lean_dec_ref(x_39);
x_11 = x_40;
x_12 = x_41;
x_13 = x_42;
x_14 = x_43;
goto block_27;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_30);
lean_dec(x_29);
x_50 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_11 = x_50;
x_12 = x_2;
x_13 = x_28;
x_14 = x_3;
goto block_27;
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
block_10:
{
lean_object* x_8; 
x_8 = lean_array_push(x_5, x_7);
x_4 = x_6;
x_5 = x_8;
goto _start;
}
block_27:
{
lean_object* x_15; lean_object* x_16; uint32_t x_17; uint32_t x_18; uint8_t x_19; 
x_15 = lean_string_utf8_extract(x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_get(x_15, x_16);
x_18 = 97;
x_19 = lean_uint32_dec_le(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_string_utf8_set(x_15, x_16, x_17);
x_6 = x_11;
x_7 = x_20;
goto block_10;
}
else
{
uint32_t x_21; uint8_t x_22; 
x_21 = 122;
x_22 = lean_uint32_dec_le(x_17, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_string_utf8_set(x_15, x_16, x_17);
x_6 = x_11;
x_7 = x_23;
goto block_10;
}
else
{
uint32_t x_24; uint32_t x_25; lean_object* x_26; 
x_24 = 4294967264;
x_25 = lean_uint32_add(x_17, x_24);
x_26 = lean_string_utf8_set(x_15, x_16, x_25);
x_6 = x_11;
x_7 = x_26;
goto block_10;
}
}
}
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
LEAN_EXPORT lean_object* l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00Lake_toUpperCamelCaseString_spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_toUpperCamelCaseString_spec__1___redArg(x_1, x_3, x_4, x_7, x_8);
return x_9;
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
