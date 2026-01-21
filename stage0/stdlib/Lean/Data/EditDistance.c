// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: public import Init.Data.String.Basic import Init.Data.Vector.Basic
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_13 = x_8;
} else {
 lean_dec_ref(x_8);
 x_13 = lean_box(0);
}
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = lean_nat_dec_eq(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_36; uint32_t x_37; uint8_t x_38; 
x_16 = lean_nat_mod(x_3, x_2);
x_17 = l_Fin_add(x_2, x_11, x_16);
lean_dec(x_16);
x_29 = lean_array_fget_borrowed(x_4, x_17);
x_30 = lean_nat_add(x_29, x_3);
x_31 = lean_array_fget_borrowed(x_12, x_11);
x_32 = lean_nat_add(x_31, x_3);
x_36 = lean_string_utf8_get_fast(x_6, x_5);
x_37 = lean_string_utf8_get_fast(x_1, x_9);
x_38 = lean_uint32_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_fget_borrowed(x_4, x_11);
lean_dec(x_11);
x_40 = lean_nat_add(x_39, x_3);
x_33 = x_40;
goto block_35;
}
else
{
lean_object* x_41; 
x_41 = lean_array_fget_borrowed(x_4, x_11);
lean_dec(x_11);
lean_inc(x_41);
x_33 = x_41;
goto block_35;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fset(x_12, x_17, x_18);
x_20 = lean_string_utf8_next_fast(x_1, x_9);
lean_dec(x_9);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_19);
if (lean_is_scalar(x_10)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_10;
}
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_7 = x_22;
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
if (lean_is_scalar(x_13)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_13;
}
lean_ctor_set(x_42, 0, x_11);
lean_ctor_set(x_42, 1, x_12);
if (lean_is_scalar(x_10)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_10;
}
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
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
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_nat_dec_lt(x_1, x_7);
lean_dec(x_7);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
x_21 = lean_string_utf8_byte_size(x_1);
x_22 = lean_nat_dec_eq(x_16, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_39; uint8_t x_40; 
x_23 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_23);
x_24 = lean_array_fset(x_20, x_4, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_mod(x_4, x_5);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_26);
lean_ctor_set(x_11, 0, x_25);
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_6, x_5, x_3, x_19, x_16, x_1, x_11);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_string_utf8_next_fast(x_1, x_16);
lean_dec(x_16);
x_39 = lean_array_get_size(x_30);
x_40 = lean_nat_dec_lt(x_25, x_39);
if (x_40 == 0)
{
lean_dec(x_2);
goto block_38;
}
else
{
if (x_40 == 0)
{
lean_dec(x_2);
goto block_38;
}
else
{
size_t x_41; size_t x_42; uint8_t x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_39);
x_43 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_30, x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_2);
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_30);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_30);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_8 = x_47;
goto _start;
}
}
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_30);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_14)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_14;
}
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_10)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_10;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_14)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_14;
}
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_11);
if (lean_is_scalar(x_10)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_10;
}
lean_ctor_set(x_50, 0, x_2);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_string_utf8_byte_size(x_1);
x_54 = lean_nat_dec_eq(x_16, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_72; uint8_t x_73; 
x_55 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_55);
x_56 = lean_array_fset(x_52, x_4, x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_mod(x_4, x_5);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_11, 1, x_59);
lean_ctor_set(x_11, 0, x_57);
x_60 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_6, x_5, x_3, x_51, x_16, x_1, x_11);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_string_utf8_next_fast(x_1, x_16);
lean_dec(x_16);
x_72 = lean_array_get_size(x_63);
x_73 = lean_nat_dec_lt(x_57, x_72);
if (x_73 == 0)
{
lean_dec(x_2);
goto block_71;
}
else
{
if (x_73 == 0)
{
lean_dec(x_2);
goto block_71;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_72);
x_76 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_63, x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_2);
goto block_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_51);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_63);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_63);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_55);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_2);
lean_ctor_set(x_80, 1, x_79);
x_8 = x_80;
goto _start;
}
}
}
block_71:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_14)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_14;
}
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_10)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_10;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_52);
lean_ctor_set(x_11, 1, x_82);
if (lean_is_scalar(x_14)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_14;
}
lean_ctor_set(x_83, 0, x_13);
lean_ctor_set(x_83, 1, x_11);
if (lean_is_scalar(x_10)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_10;
}
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_11, 0);
lean_inc(x_85);
lean_dec(x_11);
x_86 = lean_ctor_get(x_12, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_12, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_88 = x_12;
} else {
 lean_dec_ref(x_12);
 x_88 = lean_box(0);
}
x_89 = lean_string_utf8_byte_size(x_1);
x_90 = lean_nat_dec_eq(x_85, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_109; uint8_t x_110; 
x_91 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_91);
x_92 = lean_array_fset(x_87, x_4, x_91);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_mod(x_4, x_5);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_6, x_5, x_3, x_86, x_85, x_1, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_string_utf8_next_fast(x_1, x_85);
lean_dec(x_85);
x_109 = lean_array_get_size(x_100);
x_110 = lean_nat_dec_lt(x_93, x_109);
if (x_110 == 0)
{
lean_dec(x_2);
goto block_108;
}
else
{
if (x_110 == 0)
{
lean_dec(x_2);
goto block_108;
}
else
{
size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_109);
x_113 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_100, x_111, x_112);
if (x_113 == 0)
{
lean_dec(x_2);
goto block_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_86);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_100);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_100);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_102);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_91);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_2);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_2);
lean_ctor_set(x_117, 1, x_116);
x_8 = x_117;
goto _start;
}
}
}
block_108:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_86);
lean_ctor_set(x_104, 1, x_100);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_14)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_14;
}
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_105);
if (lean_is_scalar(x_10)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_10;
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_88)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_88;
}
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_87);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_85);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_14)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_14;
}
lean_ctor_set(x_121, 0, x_13);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_10)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_10;
}
lean_ctor_set(x_122, 0, x_2);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_10 = x_8;
} else {
 lean_dec_ref(x_8);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
x_21 = lean_string_utf8_byte_size(x_4);
x_22 = lean_nat_dec_eq(x_16, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_39; uint8_t x_40; 
x_23 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_23);
x_24 = lean_array_fset(x_20, x_6, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_mod(x_6, x_2);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_26);
lean_ctor_set(x_11, 0, x_25);
x_27 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_19, x_16, x_4, x_11);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_string_utf8_next_fast(x_4, x_16);
lean_dec(x_16);
x_39 = lean_array_get_size(x_30);
x_40 = lean_nat_dec_lt(x_25, x_39);
if (x_40 == 0)
{
lean_dec(x_5);
goto block_38;
}
else
{
if (x_40 == 0)
{
lean_dec(x_5);
goto block_38;
}
else
{
size_t x_41; size_t x_42; uint8_t x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_39);
x_43 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_30, x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_5);
goto block_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_30);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_30);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_5);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_5, x_3, x_6, x_2, x_1, x_7, x_47);
return x_48;
}
}
}
block_38:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_31;
}
lean_ctor_set(x_34, 0, x_19);
lean_ctor_set(x_34, 1, x_30);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
if (lean_is_scalar(x_14)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_14;
}
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_35);
if (lean_is_scalar(x_10)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_10;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
if (lean_is_scalar(x_14)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_14;
}
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_11);
if (lean_is_scalar(x_10)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_10;
}
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_string_utf8_byte_size(x_4);
x_54 = lean_nat_dec_eq(x_16, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_72; uint8_t x_73; 
x_55 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_55);
x_56 = lean_array_fset(x_52, x_6, x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_mod(x_6, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_11, 1, x_59);
lean_ctor_set(x_11, 0, x_57);
x_60 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_51, x_16, x_4, x_11);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_string_utf8_next_fast(x_4, x_16);
lean_dec(x_16);
x_72 = lean_array_get_size(x_63);
x_73 = lean_nat_dec_lt(x_57, x_72);
if (x_73 == 0)
{
lean_dec(x_5);
goto block_71;
}
else
{
if (x_73 == 0)
{
lean_dec(x_5);
goto block_71;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_72);
x_76 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_63, x_74, x_75);
if (x_76 == 0)
{
lean_dec(x_5);
goto block_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_51);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_63);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_63);
lean_ctor_set(x_77, 1, x_63);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_55);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_5);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_5, x_3, x_6, x_2, x_1, x_7, x_80);
return x_81;
}
}
}
block_71:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_64;
}
lean_ctor_set(x_67, 0, x_51);
lean_ctor_set(x_67, 1, x_63);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
if (lean_is_scalar(x_14)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_14;
}
lean_ctor_set(x_69, 0, x_55);
lean_ctor_set(x_69, 1, x_68);
if (lean_is_scalar(x_10)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_10;
}
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_51);
lean_ctor_set(x_82, 1, x_52);
lean_ctor_set(x_11, 1, x_82);
if (lean_is_scalar(x_14)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_14;
}
lean_ctor_set(x_83, 0, x_13);
lean_ctor_set(x_83, 1, x_11);
if (lean_is_scalar(x_10)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_10;
}
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_11, 0);
lean_inc(x_85);
lean_dec(x_11);
x_86 = lean_ctor_get(x_12, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_12, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_88 = x_12;
} else {
 lean_dec_ref(x_12);
 x_88 = lean_box(0);
}
x_89 = lean_string_utf8_byte_size(x_4);
x_90 = lean_nat_dec_eq(x_85, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_109; uint8_t x_110; 
x_91 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
lean_inc(x_91);
x_92 = lean_array_fset(x_87, x_6, x_91);
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_nat_mod(x_6, x_2);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_86, x_85, x_4, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
x_102 = lean_string_utf8_next_fast(x_4, x_85);
lean_dec(x_85);
x_109 = lean_array_get_size(x_100);
x_110 = lean_nat_dec_lt(x_93, x_109);
if (x_110 == 0)
{
lean_dec(x_5);
goto block_108;
}
else
{
if (x_110 == 0)
{
lean_dec(x_5);
goto block_108;
}
else
{
size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = 0;
x_112 = lean_usize_of_nat(x_109);
x_113 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_7, x_100, x_111, x_112);
if (x_113 == 0)
{
lean_dec(x_5);
goto block_108;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_86);
lean_dec(x_14);
lean_dec(x_10);
lean_inc(x_100);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_100);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_102);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_91);
lean_ctor_set(x_116, 1, x_115);
lean_inc(x_5);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_5);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_5, x_3, x_6, x_2, x_1, x_7, x_117);
return x_118;
}
}
}
block_108:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
if (lean_is_scalar(x_101)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_101;
}
lean_ctor_set(x_104, 0, x_86);
lean_ctor_set(x_104, 1, x_100);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_14)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_14;
}
lean_ctor_set(x_106, 0, x_91);
lean_ctor_set(x_106, 1, x_105);
if (lean_is_scalar(x_10)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_10;
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
if (lean_is_scalar(x_88)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_88;
}
lean_ctor_set(x_119, 0, x_86);
lean_ctor_set(x_119, 1, x_87);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_85);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_14)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_14;
}
lean_ctor_set(x_121, 0, x_13);
lean_ctor_set(x_121, 1, x_120);
if (lean_is_scalar(x_10)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_10;
}
lean_ctor_set(x_122, 0, x_5);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_9;
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
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_2, x_11, x_10, x_1, x_16, x_12, x_3, x_20);
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
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
