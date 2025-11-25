// Lean compiler output
// Module: Init.Data.String.Repr
// Imports: public import Init.Data.String.Substring import Init.Data.String.Search
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
LEAN_EXPORT lean_object* l_panic___at___00String_toInt_x21_spec__0(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
extern lean_object* l_Int_instInhabited;
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_isInt_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
static lean_object* l_String_toInt_x21___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Substring_Raw_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0___boxed(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object*);
LEAN_EXPORT uint8_t l_String_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_isInt_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_toInt_x3f(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
x_36 = l_String_Slice_Pos_get_x3f(x_35, x_33);
lean_dec_ref(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint32_t x_37; 
x_37 = 65;
x_2 = x_37;
goto block_32;
}
else
{
lean_object* x_38; uint32_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_unbox_uint32(x_38);
lean_dec(x_38);
x_2 = x_39;
goto block_32;
}
block_32:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 45;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_toNat_x3f(x_7);
lean_dec_ref(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_nat_to_int(x_11);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_nat_to_int(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_byte_size(x_1);
lean_inc(x_17);
lean_inc_ref(x_1);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Substring_Raw_nextn(x_18, x_19, x_16);
lean_dec_ref(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_17);
x_22 = l_Substring_Raw_toNat_x3f(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_int_neg(x_26);
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_neg(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_sub(x_4, x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint32_t x_14; uint32_t x_15; uint8_t x_16; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_nat_sub(x_8, x_3);
lean_dec(x_8);
x_14 = lean_string_utf8_get_fast(x_2, x_3);
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_14);
if (x_16 == 0)
{
x_10 = x_16;
goto block_13;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_14, x_17);
x_10 = x_18;
goto block_13;
}
block_13:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_9);
return x_12;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00String_isInt_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_10 = lean_string_utf8_get(x_2, x_4);
x_11 = 48;
x_12 = lean_uint32_dec_le(x_11, x_10);
if (x_12 == 0)
{
x_6 = x_12;
goto block_9;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 57;
x_14 = lean_uint32_dec_le(x_10, x_13);
x_6 = x_14;
goto block_9;
}
}
block_9:
{
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
}
}
LEAN_EXPORT uint8_t l_String_isInt(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_String_Slice_Pos_get_x3f(x_26, x_24);
lean_dec_ref(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint32_t x_28; 
x_28 = 65;
x_2 = x_28;
goto block_23;
}
else
{
lean_object* x_29; uint32_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_unbox_uint32(x_29);
lean_dec(x_29);
x_2 = x_30;
goto block_23;
}
block_23:
{
uint32_t x_3; uint8_t x_4; 
x_3 = 45;
x_4 = lean_uint32_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_5);
x_9 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0(x_8, x_6);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_nat_sub(x_11, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = lean_nat_dec_eq(x_12, x_6);
lean_dec(x_12);
return x_13;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_4;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_string_utf8_byte_size(x_1);
lean_inc(x_15);
lean_inc_ref(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Substring_Raw_nextn(x_16, x_17, x_14);
lean_dec_ref(x_16);
x_19 = lean_nat_sub(x_15, x_18);
x_20 = lean_nat_dec_eq(x_19, x_14);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_String_anyAux___at___00String_isInt_spec__2(x_20, x_1, x_15, x_18);
lean_dec(x_15);
lean_dec_ref(x_1);
if (x_21 == 0)
{
return x_4;
}
else
{
return x_20;
}
}
else
{
uint8_t x_22; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec_ref(x_1);
x_22 = 0;
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_isInt_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00String_isInt_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___00String_isInt_spec__2(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_String_isInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_isInt(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_toInt_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Int_instInhabited;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_toInt_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int expected", 12, 12);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_toInt_x21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_toInt_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_String_toInt_x21___closed__0;
x_4 = l_panic___at___00String_toInt_x21_spec__0(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
return x_5;
}
}
}
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Repr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_toInt_x21___closed__0 = _init_l_String_toInt_x21___closed__0();
lean_mark_persistent(l_String_toInt_x21___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
