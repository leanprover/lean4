// Lean compiler output
// Module: Lean.Data.EditDistance
// Imports: public import Init
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
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
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_14 = x_8;
} else {
 lean_dec_ref(x_8);
 x_14 = lean_box(0);
}
x_15 = lean_string_utf8_byte_size(x_10);
x_16 = lean_nat_dec_lt(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
if (lean_is_scalar(x_14)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_14;
}
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_41; uint32_t x_42; uint8_t x_43; 
lean_inc(x_11);
lean_inc_ref(x_10);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_19 = x_7;
} else {
 lean_dec_ref(x_7);
 x_19 = lean_box(0);
}
x_20 = lean_nat_mod(x_2, x_1);
x_21 = l_Fin_add(x_1, x_12, x_20);
lean_dec(x_20);
x_34 = lean_array_fget_borrowed(x_3, x_21);
x_35 = lean_nat_add(x_34, x_2);
x_36 = lean_array_fget_borrowed(x_13, x_12);
x_37 = lean_nat_add(x_36, x_2);
x_41 = lean_string_utf8_get_fast(x_4, x_5);
x_42 = lean_string_utf8_get_fast(x_10, x_11);
x_43 = lean_uint32_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_array_fget_borrowed(x_3, x_12);
lean_dec(x_12);
x_45 = lean_nat_add(x_44, x_2);
x_38 = x_45;
goto block_40;
}
else
{
lean_object* x_46; 
x_46 = lean_array_fget_borrowed(x_3, x_12);
lean_dec(x_12);
lean_inc(x_46);
x_38 = x_46;
goto block_40;
}
block_29:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_array_fset(x_13, x_21, x_22);
x_24 = lean_string_utf8_next_fast(x_10, x_11);
lean_dec(x_11);
if (lean_is_scalar(x_19)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_19;
}
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_24);
if (lean_is_scalar(x_14)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_14;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_9)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_9;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_6 = x_27;
goto _start;
}
block_33:
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_31, x_30);
if (x_32 == 0)
{
lean_dec(x_31);
x_22 = x_30;
goto block_29;
}
else
{
lean_dec(x_30);
x_22 = x_31;
goto block_29;
}
}
block_40:
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_37);
if (x_39 == 0)
{
lean_dec(x_35);
x_30 = x_38;
x_31 = x_37;
goto block_33;
}
else
{
lean_dec(x_37);
x_30 = x_38;
x_31 = x_35;
goto block_33;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
uint8_t x_7; uint8_t x_8; lean_object* x_13; uint8_t x_14; 
x_7 = 1;
x_13 = lean_array_uget(x_3, x_4);
x_14 = lean_nat_dec_lt(x_1, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
x_8 = x_2;
goto block_12;
}
else
{
x_8 = x_6;
goto block_12;
}
block_12:
{
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
goto _start;
}
else
{
return x_7;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_15 = x_8;
} else {
 lean_dec_ref(x_8);
 x_15 = lean_box(0);
}
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_string_utf8_byte_size(x_17);
x_22 = lean_nat_dec_lt(x_18, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_5);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_45; lean_object* x_52; uint8_t x_53; 
x_26 = lean_ctor_get(x_12, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_12, 0);
lean_dec(x_27);
x_28 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_28);
x_29 = lean_array_fset(x_20, x_3, x_28);
x_30 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_5);
x_31 = lean_nat_mod(x_3, x_4);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_31);
x_32 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_4, x_2, x_19, x_17, x_18, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
x_52 = lean_array_get_size(x_35);
x_53 = lean_nat_dec_lt(x_30, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
x_45 = x_22;
goto block_51;
}
else
{
if (x_53 == 0)
{
lean_dec(x_52);
x_45 = x_22;
goto block_51;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_56 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_6, x_22, x_35, x_54, x_55);
if (x_56 == 0)
{
x_45 = x_22;
goto block_51;
}
else
{
lean_dec(x_19);
goto block_44;
}
}
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_inc(x_35);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_35);
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_9;
}
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
x_7 = x_42;
goto _start;
}
block_51:
{
if (x_45 == 0)
{
lean_dec(x_19);
goto block_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_46 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_35);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_75; lean_object* x_82; uint8_t x_83; 
lean_dec(x_12);
x_57 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_57);
x_58 = lean_array_fset(x_20, x_3, x_57);
x_59 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_5);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_nat_mod(x_3, x_4);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_61);
lean_ctor_set(x_10, 0, x_60);
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_4, x_2, x_19, x_17, x_18, x_10);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_67);
x_82 = lean_array_get_size(x_65);
x_83 = lean_nat_dec_lt(x_59, x_82);
if (x_83 == 0)
{
lean_dec(x_82);
x_75 = x_22;
goto block_81;
}
else
{
if (x_83 == 0)
{
lean_dec(x_82);
x_75 = x_22;
goto block_81;
}
else
{
size_t x_84; size_t x_85; uint8_t x_86; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_86 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_6, x_22, x_65, x_84, x_85);
if (x_86 == 0)
{
x_75 = x_22;
goto block_81;
}
else
{
lean_dec(x_19);
goto block_74;
}
}
}
block_74:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_65);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_15)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_15;
}
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_9;
}
lean_ctor_set(x_72, 0, x_1);
lean_ctor_set(x_72, 1, x_71);
x_7 = x_72;
goto _start;
}
block_81:
{
if (x_75 == 0)
{
lean_dec(x_19);
goto block_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_76 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_19);
lean_ctor_set(x_77, 1, x_65);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_12, 0);
x_88 = lean_ctor_get(x_12, 1);
x_89 = lean_ctor_get(x_13, 0);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_13);
x_91 = lean_string_utf8_byte_size(x_87);
x_92 = lean_nat_dec_lt(x_88, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_5);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_10, 1, x_93);
if (lean_is_scalar(x_15)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_15;
}
lean_ctor_set(x_94, 0, x_14);
lean_ctor_set(x_94, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_9;
}
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_116; lean_object* x_123; uint8_t x_124; 
lean_inc(x_88);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_96 = x_12;
} else {
 lean_dec_ref(x_12);
 x_96 = lean_box(0);
}
x_97 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_97);
x_98 = lean_array_fset(x_90, x_3, x_97);
x_99 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_nat_mod(x_3, x_4);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_10, 1, x_102);
lean_ctor_set(x_10, 0, x_100);
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_4, x_2, x_89, x_87, x_88, x_10);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_string_utf8_next_fast(x_87, x_88);
lean_dec(x_88);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_87);
lean_ctor_set(x_109, 1, x_108);
x_123 = lean_array_get_size(x_106);
x_124 = lean_nat_dec_lt(x_99, x_123);
if (x_124 == 0)
{
lean_dec(x_123);
x_116 = x_92;
goto block_122;
}
else
{
if (x_124 == 0)
{
lean_dec(x_123);
x_116 = x_92;
goto block_122;
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = 0;
x_126 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_127 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_6, x_92, x_106, x_125, x_126);
if (x_127 == 0)
{
x_116 = x_92;
goto block_122;
}
else
{
lean_dec(x_89);
goto block_115;
}
}
}
block_115:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_106);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_105;
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_15)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_15;
}
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
x_7 = x_113;
goto _start;
}
block_122:
{
if (x_116 == 0)
{
lean_dec(x_89);
goto block_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_89);
lean_ctor_set(x_118, 1, x_106);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_97);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_128 = lean_ctor_get(x_10, 0);
x_129 = lean_ctor_get(x_10, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_10);
x_130 = lean_ctor_get(x_8, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_131 = x_8;
} else {
 lean_dec_ref(x_8);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
x_137 = lean_string_utf8_byte_size(x_132);
x_138 = lean_nat_dec_lt(x_133, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_5);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_131)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_131;
}
lean_ctor_set(x_141, 0, x_130);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_9)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_9;
}
lean_ctor_set(x_142, 0, x_1);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_164; lean_object* x_171; uint8_t x_172; 
lean_inc(x_133);
lean_inc_ref(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_143 = x_128;
} else {
 lean_dec_ref(x_128);
 x_143 = lean_box(0);
}
x_144 = lean_nat_add(x_130, x_2);
lean_dec(x_130);
lean_inc(x_144);
x_145 = lean_array_fset(x_135, x_3, x_144);
x_146 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_5);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_nat_mod(x_3, x_4);
if (lean_is_scalar(x_136)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_136;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_4, x_2, x_134, x_132, x_133, x_150);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_string_utf8_next_fast(x_132, x_133);
lean_dec(x_133);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_132);
lean_ctor_set(x_157, 1, x_156);
x_171 = lean_array_get_size(x_154);
x_172 = lean_nat_dec_lt(x_146, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
x_164 = x_138;
goto block_170;
}
else
{
if (x_172 == 0)
{
lean_dec(x_171);
x_164 = x_138;
goto block_170;
}
else
{
size_t x_173; size_t x_174; uint8_t x_175; 
x_173 = 0;
x_174 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_175 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_6, x_138, x_154, x_173, x_174);
if (x_175 == 0)
{
x_164 = x_138;
goto block_170;
}
else
{
lean_dec(x_134);
goto block_163;
}
}
}
block_163:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_inc(x_154);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_154);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_131)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_131;
}
lean_ctor_set(x_160, 0, x_144);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_9;
}
lean_ctor_set(x_161, 0, x_1);
lean_ctor_set(x_161, 1, x_160);
x_7 = x_161;
goto _start;
}
block_170:
{
if (x_164 == 0)
{
lean_dec(x_134);
goto block_163;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_131);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_165 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_134);
lean_ctor_set(x_166, 1, x_154);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_157);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_144);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_9 = x_7;
} else {
 lean_dec_ref(x_7);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_15 = x_8;
} else {
 lean_dec_ref(x_8);
 x_15 = lean_box(0);
}
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_string_utf8_byte_size(x_17);
x_22 = lean_nat_dec_lt(x_18, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_6);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_15;
}
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_9;
}
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_45; lean_object* x_52; uint8_t x_53; 
x_26 = lean_ctor_get(x_12, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_12, 0);
lean_dec(x_27);
x_28 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_28);
x_29 = lean_array_fset(x_20, x_5, x_28);
x_30 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_6);
x_31 = lean_nat_mod(x_5, x_1);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_31);
x_32 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_19, x_17, x_18, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_37 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_17);
lean_ctor_set(x_38, 1, x_37);
x_52 = lean_array_get_size(x_35);
x_53 = lean_nat_dec_lt(x_30, x_52);
if (x_53 == 0)
{
lean_dec(x_52);
x_45 = x_22;
goto block_51;
}
else
{
if (x_53 == 0)
{
lean_dec(x_52);
x_45 = x_22;
goto block_51;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = 0;
x_55 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_56 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_3, x_22, x_35, x_54, x_55);
if (x_56 == 0)
{
x_45 = x_22;
goto block_51;
}
else
{
lean_dec(x_19);
goto block_44;
}
}
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_35);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_35);
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
if (lean_is_scalar(x_15)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_15;
}
lean_ctor_set(x_41, 0, x_28);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_9;
}
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_42);
return x_43;
}
block_51:
{
if (x_45 == 0)
{
lean_dec(x_19);
goto block_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_46 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_35);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_28);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_75; lean_object* x_82; uint8_t x_83; 
lean_dec(x_12);
x_57 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_57);
x_58 = lean_array_fset(x_20, x_5, x_57);
x_59 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_nat_mod(x_5, x_1);
lean_ctor_set(x_13, 1, x_58);
lean_ctor_set(x_13, 0, x_61);
lean_ctor_set(x_10, 0, x_60);
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_19, x_17, x_18, x_10);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_17);
lean_ctor_set(x_68, 1, x_67);
x_82 = lean_array_get_size(x_65);
x_83 = lean_nat_dec_lt(x_59, x_82);
if (x_83 == 0)
{
lean_dec(x_82);
x_75 = x_22;
goto block_81;
}
else
{
if (x_83 == 0)
{
lean_dec(x_82);
x_75 = x_22;
goto block_81;
}
else
{
size_t x_84; size_t x_85; uint8_t x_86; 
x_84 = 0;
x_85 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_86 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_3, x_22, x_65, x_84, x_85);
if (x_86 == 0)
{
x_75 = x_22;
goto block_81;
}
else
{
lean_dec(x_19);
goto block_74;
}
}
}
block_74:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_inc(x_65);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_65);
lean_ctor_set(x_69, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_15)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_15;
}
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_70);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_9;
}
lean_ctor_set(x_72, 0, x_4);
lean_ctor_set(x_72, 1, x_71);
x_73 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_72);
return x_73;
}
block_81:
{
if (x_75 == 0)
{
lean_dec(x_19);
goto block_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_76 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_19);
lean_ctor_set(x_77, 1, x_65);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_57);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_87 = lean_ctor_get(x_12, 0);
x_88 = lean_ctor_get(x_12, 1);
x_89 = lean_ctor_get(x_13, 0);
x_90 = lean_ctor_get(x_13, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_13);
x_91 = lean_string_utf8_byte_size(x_87);
x_92 = lean_nat_dec_lt(x_88, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec_ref(x_6);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_10, 1, x_93);
if (lean_is_scalar(x_15)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_15;
}
lean_ctor_set(x_94, 0, x_14);
lean_ctor_set(x_94, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_9;
}
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_116; lean_object* x_123; uint8_t x_124; 
lean_inc(x_88);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_96 = x_12;
} else {
 lean_dec_ref(x_12);
 x_96 = lean_box(0);
}
x_97 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_97);
x_98 = lean_array_fset(x_90, x_5, x_97);
x_99 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
if (lean_is_scalar(x_96)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_96;
}
lean_ctor_set(x_100, 0, x_6);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_nat_mod(x_5, x_1);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_10, 1, x_102);
lean_ctor_set(x_10, 0, x_100);
x_103 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_89, x_87, x_88, x_10);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = lean_string_utf8_next_fast(x_87, x_88);
lean_dec(x_88);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_87);
lean_ctor_set(x_109, 1, x_108);
x_123 = lean_array_get_size(x_106);
x_124 = lean_nat_dec_lt(x_99, x_123);
if (x_124 == 0)
{
lean_dec(x_123);
x_116 = x_92;
goto block_122;
}
else
{
if (x_124 == 0)
{
lean_dec(x_123);
x_116 = x_92;
goto block_122;
}
else
{
size_t x_125; size_t x_126; uint8_t x_127; 
x_125 = 0;
x_126 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_127 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_3, x_92, x_106, x_125, x_126);
if (x_127 == 0)
{
x_116 = x_92;
goto block_122;
}
else
{
lean_dec(x_89);
goto block_115;
}
}
}
block_115:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_inc(x_106);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_106);
if (lean_is_scalar(x_105)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_105;
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_15)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_15;
}
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_9;
}
lean_ctor_set(x_113, 0, x_4);
lean_ctor_set(x_113, 1, x_112);
x_114 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_113);
return x_114;
}
block_122:
{
if (x_116 == 0)
{
lean_dec(x_89);
goto block_115;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_89);
lean_ctor_set(x_118, 1, x_106);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_109);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_97);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_128 = lean_ctor_get(x_10, 0);
x_129 = lean_ctor_get(x_10, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_10);
x_130 = lean_ctor_get(x_8, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_131 = x_8;
} else {
 lean_dec_ref(x_8);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_ctor_get(x_129, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_129, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_136 = x_129;
} else {
 lean_dec_ref(x_129);
 x_136 = lean_box(0);
}
x_137 = lean_string_utf8_byte_size(x_132);
x_138 = lean_nat_dec_lt(x_133, x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec_ref(x_6);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_128);
lean_ctor_set(x_140, 1, x_139);
if (lean_is_scalar(x_131)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_131;
}
lean_ctor_set(x_141, 0, x_130);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_9)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_9;
}
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_164; lean_object* x_171; uint8_t x_172; 
lean_inc(x_133);
lean_inc_ref(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_143 = x_128;
} else {
 lean_dec_ref(x_128);
 x_143 = lean_box(0);
}
x_144 = lean_nat_add(x_130, x_2);
lean_dec(x_130);
lean_inc(x_144);
x_145 = lean_array_fset(x_135, x_5, x_144);
x_146 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
if (lean_is_scalar(x_143)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_143;
}
lean_ctor_set(x_147, 0, x_6);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_nat_mod(x_5, x_1);
if (lean_is_scalar(x_136)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_136;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_145);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_134, x_132, x_133, x_150);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_string_utf8_next_fast(x_132, x_133);
lean_dec(x_133);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_132);
lean_ctor_set(x_157, 1, x_156);
x_171 = lean_array_get_size(x_154);
x_172 = lean_nat_dec_lt(x_146, x_171);
if (x_172 == 0)
{
lean_dec(x_171);
x_164 = x_138;
goto block_170;
}
else
{
if (x_172 == 0)
{
lean_dec(x_171);
x_164 = x_138;
goto block_170;
}
else
{
size_t x_173; size_t x_174; uint8_t x_175; 
x_173 = 0;
x_174 = lean_usize_of_nat(x_171);
lean_dec(x_171);
x_175 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_3, x_138, x_154, x_173, x_174);
if (x_175 == 0)
{
x_164 = x_138;
goto block_170;
}
else
{
lean_dec(x_134);
goto block_163;
}
}
}
block_163:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_inc(x_154);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_154);
if (lean_is_scalar(x_153)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_153;
}
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_131)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_131;
}
lean_ctor_set(x_160, 0, x_144);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_9;
}
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_160);
x_162 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_161);
return x_162;
}
block_170:
{
if (x_164 == 0)
{
lean_dec(x_134);
goto block_163;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_131);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_165 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_134);
lean_ctor_set(x_166, 1, x_154);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_157);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_144);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_33; uint8_t x_36; 
x_4 = lean_string_length(x_1);
x_5 = lean_string_length(x_2);
x_36 = lean_nat_dec_le(x_4, x_5);
if (x_36 == 0)
{
lean_inc(x_4);
x_33 = x_4;
goto block_35;
}
else
{
lean_inc(x_5);
x_33 = x_5;
goto block_35;
}
block_32:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
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
x_15 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_14, x_13, x_12);
lean_dec_ref(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_11, x_10, x_3, x_17, x_12, x_2, x_21);
lean_dec(x_11);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec_ref(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_fget(x_27, x_5);
lean_dec(x_5);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_5);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec_ref(x_26);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_box(0);
return x_31;
}
}
block_35:
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_4, x_5);
if (x_34 == 0)
{
lean_dec(x_4);
lean_inc(x_5);
x_6 = x_33;
x_7 = x_5;
goto block_32;
}
else
{
x_6 = x_33;
x_7 = x_4;
goto block_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___00Lean_EditDistance_levenshtein_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EditDistance_levenshtein(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
