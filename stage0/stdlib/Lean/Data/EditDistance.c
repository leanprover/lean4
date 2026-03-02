// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: public import Init.Data.String.Basic import Init.Data.Vector.Basic import Init.Data.Nat.Order import Init.Data.Order.Lemmas import Init.Data.Range import Init.While
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0_value;
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_7 = lean_array_fset(x_2, x_3, x_3);
x_8 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_12 = x_7;
} else {
 lean_dec_ref(x_7);
 x_12 = lean_box(0);
}
x_13 = lean_string_utf8_byte_size(x_1);
x_14 = lean_nat_dec_eq(x_8, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_mod(x_15, x_2);
x_17 = l_Fin_add(x_2, x_10, x_16);
lean_dec(x_16);
x_29 = lean_array_fget_borrowed(x_3, x_17);
x_30 = lean_nat_add(x_29, x_15);
x_31 = lean_array_fget_borrowed(x_11, x_10);
x_32 = lean_nat_add(x_31, x_15);
x_36 = lean_string_utf8_get_fast(x_5, x_4);
x_37 = lean_string_utf8_get_fast(x_1, x_8);
x_38 = lean_uint32_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_fget_borrowed(x_3, x_10);
lean_dec(x_10);
x_40 = lean_nat_add(x_39, x_15);
x_33 = x_40;
goto block_35;
}
else
{
lean_object* x_41; 
x_41 = lean_array_fget_borrowed(x_3, x_10);
lean_dec(x_10);
lean_inc(x_41);
x_33 = x_41;
goto block_35;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fset(x_11, x_17, x_18);
x_20 = lean_string_utf8_next_fast(x_1, x_8);
lean_dec(x_8);
if (lean_is_scalar(x_12)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_12;
}
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_9)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_9;
}
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_6 = x_22;
goto _start;
}
block_28:
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_26, x_25);
if (x_27 == 0)
{
lean_dec(x_26);
x_18 = x_25;
goto block_24;
}
else
{
lean_dec(x_25);
x_18 = x_26;
goto block_24;
}
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_32);
if (x_34 == 0)
{
lean_dec(x_30);
x_25 = x_33;
x_26 = x_32;
goto block_28;
}
else
{
lean_dec(x_32);
x_25 = x_33;
x_26 = x_30;
goto block_28;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_12)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_12;
}
lean_ctor_set(x_42, 0, x_10);
lean_ctor_set(x_42, 1, x_11);
if (lean_is_scalar(x_9)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_9;
}
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 1;
x_7 = lean_array_uget_borrowed(x_2, x_3);
x_8 = lean_nat_dec_lt(x_1, x_7);
if (x_8 == 0)
{
return x_6;
}
else
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_box(0);
x_19 = lean_string_utf8_byte_size(x_1);
x_20 = lean_nat_dec_eq(x_13, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_38; uint8_t x_39; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_add(x_10, x_21);
lean_dec(x_10);
lean_inc(x_23);
x_24 = lean_array_fset(x_17, x_22, x_23);
x_25 = lean_nat_mod(x_22, x_2);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_8, 0, x_22);
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_3, x_2, x_16, x_13, x_1, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_string_utf8_next_fast(x_1, x_13);
lean_dec(x_13);
x_38 = lean_array_get_size(x_29);
x_39 = lean_nat_dec_lt(x_22, x_38);
if (x_39 == 0)
{
goto block_37;
}
else
{
if (x_39 == 0)
{
goto block_37;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_38);
x_42 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_29, x_40, x_41);
if (x_42 == 0)
{
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_29);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_45);
x_5 = x_46;
goto _start;
}
}
}
block_37:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_29);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
if (lean_is_scalar(x_11)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_11;
}
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_7)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_7;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_11)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_11;
}
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_8);
if (lean_is_scalar(x_7)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_7;
}
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = lean_box(0);
x_53 = lean_string_utf8_byte_size(x_1);
x_54 = lean_nat_dec_eq(x_13, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_73; uint8_t x_74; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_add(x_10, x_55);
lean_dec(x_10);
lean_inc(x_57);
x_58 = lean_array_fset(x_51, x_56, x_57);
x_59 = lean_nat_mod(x_56, x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_8, 1, x_60);
lean_ctor_set(x_8, 0, x_56);
x_61 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_3, x_2, x_50, x_13, x_1, x_8);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_string_utf8_next_fast(x_1, x_13);
lean_dec(x_13);
x_73 = lean_array_get_size(x_64);
x_74 = lean_nat_dec_lt(x_56, x_73);
if (x_74 == 0)
{
goto block_72;
}
else
{
if (x_74 == 0)
{
goto block_72;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_73);
x_77 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_64, x_75, x_76);
if (x_77 == 0)
{
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_50);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_64);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_64);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_57);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_52);
lean_ctor_set(x_81, 1, x_80);
x_5 = x_81;
goto _start;
}
}
}
block_72:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_64);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_11)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_11;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_7)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_7;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_51);
lean_ctor_set(x_8, 1, x_83);
if (lean_is_scalar(x_11)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_11;
}
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_8);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_52);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
lean_dec(x_8);
x_87 = lean_ctor_get(x_9, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_9, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_89 = x_9;
} else {
 lean_dec_ref(x_9);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
x_91 = lean_string_utf8_byte_size(x_1);
x_92 = lean_nat_dec_eq(x_86, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_112; uint8_t x_113; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_add(x_10, x_93);
lean_dec(x_10);
lean_inc(x_95);
x_96 = lean_array_fset(x_88, x_94, x_95);
x_97 = lean_nat_mod(x_94, x_2);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
x_100 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_3, x_2, x_87, x_86, x_1, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_string_utf8_next_fast(x_1, x_86);
lean_dec(x_86);
x_112 = lean_array_get_size(x_103);
x_113 = lean_nat_dec_lt(x_94, x_112);
if (x_113 == 0)
{
goto block_111;
}
else
{
if (x_113 == 0)
{
goto block_111;
}
else
{
size_t x_114; size_t x_115; uint8_t x_116; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_112);
x_116 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_103, x_114, x_115);
if (x_116 == 0)
{
goto block_111;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_103);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_95);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_90);
lean_ctor_set(x_120, 1, x_119);
x_5 = x_120;
goto _start;
}
}
}
block_111:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_87);
lean_ctor_set(x_107, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_11)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_11;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_7)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_7;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_scalar(x_89)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_89;
}
lean_ctor_set(x_122, 0, x_87);
lean_ctor_set(x_122, 1, x_88);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_86);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_11)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_11;
}
lean_ctor_set(x_124, 0, x_10);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_90);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_8, 0);
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_box(0);
x_19 = lean_string_utf8_byte_size(x_3);
x_20 = lean_nat_dec_eq(x_13, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_38; uint8_t x_39; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_add(x_10, x_21);
lean_dec(x_10);
lean_inc(x_23);
x_24 = lean_array_fset(x_17, x_22, x_23);
x_25 = lean_nat_mod(x_22, x_2);
lean_ctor_set(x_9, 1, x_24);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_8, 0, x_22);
x_26 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_16, x_13, x_3, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_string_utf8_next_fast(x_3, x_13);
lean_dec(x_13);
x_38 = lean_array_get_size(x_29);
x_39 = lean_nat_dec_lt(x_22, x_38);
if (x_39 == 0)
{
goto block_37;
}
else
{
if (x_39 == 0)
{
goto block_37;
}
else
{
size_t x_40; size_t x_41; uint8_t x_42; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_38);
x_42 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_29, x_40, x_41);
if (x_42 == 0)
{
goto block_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_29);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_29);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_23);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_3, x_2, x_1, x_4, x_46);
return x_47;
}
}
}
block_37:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_16);
lean_ctor_set(x_33, 1, x_29);
if (lean_is_scalar(x_28)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_28;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
if (lean_is_scalar(x_11)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_11;
}
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_7)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_7;
}
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
if (lean_is_scalar(x_11)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_11;
}
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_8);
if (lean_is_scalar(x_7)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_7;
}
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_9, 0);
x_51 = lean_ctor_get(x_9, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_9);
x_52 = lean_box(0);
x_53 = lean_string_utf8_byte_size(x_3);
x_54 = lean_nat_dec_eq(x_13, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_73; uint8_t x_74; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_add(x_10, x_55);
lean_dec(x_10);
lean_inc(x_57);
x_58 = lean_array_fset(x_51, x_56, x_57);
x_59 = lean_nat_mod(x_56, x_2);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_8, 1, x_60);
lean_ctor_set(x_8, 0, x_56);
x_61 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_50, x_13, x_3, x_8);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_string_utf8_next_fast(x_3, x_13);
lean_dec(x_13);
x_73 = lean_array_get_size(x_64);
x_74 = lean_nat_dec_lt(x_56, x_73);
if (x_74 == 0)
{
goto block_72;
}
else
{
if (x_74 == 0)
{
goto block_72;
}
else
{
size_t x_75; size_t x_76; uint8_t x_77; 
x_75 = 0;
x_76 = lean_usize_of_nat(x_73);
x_77 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_64, x_75, x_76);
if (x_77 == 0)
{
goto block_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_50);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_64);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_64);
lean_ctor_set(x_78, 1, x_64);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_66);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_57);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_52);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_3, x_2, x_1, x_4, x_81);
return x_82;
}
}
}
block_72:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_50);
lean_ctor_set(x_68, 1, x_64);
if (lean_is_scalar(x_63)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_63;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_11)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_11;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_7)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_7;
}
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_51);
lean_ctor_set(x_8, 1, x_83);
if (lean_is_scalar(x_11)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_11;
}
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_8);
if (lean_is_scalar(x_7)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_7;
}
lean_ctor_set(x_85, 0, x_52);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
lean_dec(x_8);
x_87 = lean_ctor_get(x_9, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_9, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_89 = x_9;
} else {
 lean_dec_ref(x_9);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
x_91 = lean_string_utf8_byte_size(x_3);
x_92 = lean_nat_dec_eq(x_86, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_112; uint8_t x_113; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_add(x_10, x_93);
lean_dec(x_10);
lean_inc(x_95);
x_96 = lean_array_fset(x_88, x_94, x_95);
x_97 = lean_nat_mod(x_94, x_2);
if (lean_is_scalar(x_89)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_89;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_94);
lean_ctor_set(x_99, 1, x_98);
x_100 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_87, x_86, x_3, x_99);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_string_utf8_next_fast(x_3, x_86);
lean_dec(x_86);
x_112 = lean_array_get_size(x_103);
x_113 = lean_nat_dec_lt(x_94, x_112);
if (x_113 == 0)
{
goto block_111;
}
else
{
if (x_113 == 0)
{
goto block_111;
}
else
{
size_t x_114; size_t x_115; uint8_t x_116; 
x_114 = 0;
x_115 = lean_usize_of_nat(x_112);
x_116 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_103, x_114, x_115);
if (x_116 == 0)
{
goto block_111;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_87);
lean_dec(x_11);
lean_dec(x_7);
lean_inc(x_103);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_103);
lean_ctor_set(x_117, 1, x_103);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_95);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_90);
lean_ctor_set(x_120, 1, x_119);
x_121 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_3, x_2, x_1, x_4, x_120);
return x_121;
}
}
}
block_111:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_87);
lean_ctor_set(x_107, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_11)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_11;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_7)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_7;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_scalar(x_89)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_89;
}
lean_ctor_set(x_122, 0, x_87);
lean_ctor_set(x_122, 1, x_88);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_86);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_11)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_11;
}
lean_ctor_set(x_124, 0, x_10);
lean_ctor_set(x_124, 1, x_123);
if (lean_is_scalar(x_7)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_7;
}
lean_ctor_set(x_125, 0, x_90);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_32; uint8_t x_35; 
x_4 = lean_string_length(x_1);
x_5 = lean_string_length(x_2);
x_35 = lean_nat_dec_le(x_4, x_5);
if (x_35 == 0)
{
x_32 = x_4;
goto block_34;
}
else
{
x_32 = x_5;
goto block_34;
}
block_31:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_13 = lean_mk_array(x_11, x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_10);
lean_inc_ref(x_13);
x_15 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_14, x_13, x_12);
lean_dec_ref(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_2, x_11, x_1, x_3, x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec_ref(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_fget(x_26, x_5);
lean_dec(x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec_ref(x_25);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_box(0);
return x_30;
}
}
block_34:
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_4, x_5);
if (x_33 == 0)
{
x_6 = x_32;
x_7 = x_5;
goto block_31;
}
else
{
x_6 = x_32;
x_7 = x_4;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EditDistance_levenshtein(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Range(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
