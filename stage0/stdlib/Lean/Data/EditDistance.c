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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_EditDistance_levenshtein(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_14 = lean_string_utf8_byte_size(x_9);
x_15 = lean_nat_dec_lt(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
if (lean_is_scalar(x_8)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_8;
}
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_42; uint32_t x_43; uint8_t x_44; 
lean_inc(x_10);
lean_inc_ref(x_9);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_18 = x_6;
} else {
 lean_dec_ref(x_6);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_nat_mod(x_3, x_2);
x_22 = l_Fin_add(x_2, x_11, x_21);
lean_dec(x_21);
x_35 = lean_array_fget_borrowed(x_4, x_22);
x_36 = lean_nat_add(x_35, x_3);
x_37 = lean_array_fget_borrowed(x_12, x_11);
x_38 = lean_nat_add(x_37, x_3);
x_42 = lean_string_utf8_get_fast(x_19, x_20);
x_43 = lean_string_utf8_get_fast(x_9, x_10);
x_44 = lean_uint32_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_fget_borrowed(x_4, x_11);
lean_dec(x_11);
x_46 = lean_nat_add(x_45, x_3);
x_39 = x_46;
goto block_41;
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget_borrowed(x_4, x_11);
lean_dec(x_11);
lean_inc(x_47);
x_39 = x_47;
goto block_41;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_fset(x_12, x_22, x_23);
x_25 = lean_string_utf8_next_fast(x_9, x_10);
lean_dec(x_10);
if (lean_is_scalar(x_18)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_18;
}
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
if (lean_is_scalar(x_13)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_13;
}
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_24);
if (lean_is_scalar(x_8)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_8;
}
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_5 = x_28;
goto _start;
}
block_34:
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
lean_dec(x_32);
x_23 = x_31;
goto block_30;
}
else
{
lean_dec(x_31);
x_23 = x_32;
goto block_30;
}
}
block_41:
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_36, x_38);
if (x_40 == 0)
{
lean_dec(x_36);
x_31 = x_39;
x_32 = x_38;
goto block_34;
}
else
{
lean_dec(x_38);
x_31 = x_39;
x_32 = x_36;
goto block_34;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_43; lean_object* x_50; uint8_t x_51; 
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_25);
x_26 = lean_array_fset(x_20, x_3, x_25);
x_27 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_nat_mod(x_3, x_4);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_10, 0, x_28);
x_30 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_12, x_4, x_2, x_19, x_10);
lean_dec(x_12);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_50 = lean_array_get_size(x_33);
x_51 = lean_nat_dec_lt(x_27, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
x_43 = x_22;
goto block_49;
}
else
{
if (x_51 == 0)
{
lean_dec(x_50);
x_43 = x_22;
goto block_49;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_54 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_6, x_22, x_33, x_52, x_53);
if (x_54 == 0)
{
x_43 = x_22;
goto block_49;
}
else
{
lean_dec(x_19);
goto block_42;
}
}
}
block_42:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_33);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_33);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_15)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_15;
}
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_9;
}
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_39);
x_7 = x_40;
goto _start;
}
block_49:
{
if (x_43 == 0)
{
lean_dec(x_19);
goto block_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_44 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_33);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_string_utf8_byte_size(x_55);
x_60 = lean_nat_dec_lt(x_56, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_10, 1, x_61);
if (lean_is_scalar(x_15)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_15;
}
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_9;
}
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_83; lean_object* x_90; uint8_t x_91; 
lean_inc(x_56);
lean_inc_ref(x_55);
x_64 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_64);
x_65 = lean_array_fset(x_58, x_3, x_64);
x_66 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_5);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_nat_mod(x_3, x_4);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_10, 1, x_69);
lean_ctor_set(x_10, 0, x_67);
x_70 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_12, x_4, x_2, x_57, x_10);
lean_dec(x_12);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_string_utf8_next_fast(x_55, x_56);
lean_dec(x_56);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_55);
lean_ctor_set(x_76, 1, x_75);
x_90 = lean_array_get_size(x_73);
x_91 = lean_nat_dec_lt(x_66, x_90);
if (x_91 == 0)
{
lean_dec(x_90);
x_83 = x_60;
goto block_89;
}
else
{
if (x_91 == 0)
{
lean_dec(x_90);
x_83 = x_60;
goto block_89;
}
else
{
size_t x_92; size_t x_93; uint8_t x_94; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_94 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_6, x_60, x_73, x_92, x_93);
if (x_94 == 0)
{
x_83 = x_60;
goto block_89;
}
else
{
lean_dec(x_57);
goto block_82;
}
}
}
block_82:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_73);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_73);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_15)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_15;
}
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_9;
}
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_79);
x_7 = x_80;
goto _start;
}
block_89:
{
if (x_83 == 0)
{
lean_dec(x_57);
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_84 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_57);
lean_ctor_set(x_85, 1, x_73);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_64);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_ctor_get(x_8, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_98 = x_8;
} else {
 lean_dec_ref(x_8);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_string_utf8_byte_size(x_99);
x_105 = lean_nat_dec_lt(x_100, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_5);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_98)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_98;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_130; lean_object* x_137; uint8_t x_138; 
lean_inc(x_100);
lean_inc_ref(x_99);
x_110 = lean_nat_add(x_97, x_2);
lean_dec(x_97);
lean_inc(x_110);
x_111 = lean_array_fset(x_102, x_3, x_110);
x_112 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_5);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_5);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_nat_mod(x_3, x_4);
if (lean_is_scalar(x_103)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_103;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_95, x_4, x_2, x_101, x_116);
lean_dec(x_95);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_string_utf8_next_fast(x_99, x_100);
lean_dec(x_100);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_99);
lean_ctor_set(x_123, 1, x_122);
x_137 = lean_array_get_size(x_120);
x_138 = lean_nat_dec_lt(x_112, x_137);
if (x_138 == 0)
{
lean_dec(x_137);
x_130 = x_105;
goto block_136;
}
else
{
if (x_138 == 0)
{
lean_dec(x_137);
x_130 = x_105;
goto block_136;
}
else
{
size_t x_139; size_t x_140; uint8_t x_141; 
x_139 = 0;
x_140 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_141 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_6, x_105, x_120, x_139, x_140);
if (x_141 == 0)
{
x_130 = x_105;
goto block_136;
}
else
{
lean_dec(x_101);
goto block_129;
}
}
}
block_129:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_inc(x_120);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_120);
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_119;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_98)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_98;
}
lean_ctor_set(x_126, 0, x_110);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_1);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_126);
x_7 = x_127;
goto _start;
}
block_136:
{
if (x_130 == 0)
{
lean_dec(x_101);
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_98);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec(x_1);
x_131 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_101);
lean_ctor_set(x_132, 1, x_120);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_110);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_43; lean_object* x_50; uint8_t x_51; 
lean_inc(x_18);
lean_inc_ref(x_17);
x_25 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_25);
x_26 = lean_array_fset(x_20, x_5, x_25);
x_27 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_nat_mod(x_5, x_1);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_29);
lean_ctor_set(x_10, 0, x_28);
x_30 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_12, x_1, x_2, x_19, x_10);
lean_dec(x_12);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_string_utf8_next_fast(x_17, x_18);
lean_dec(x_18);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_35);
x_50 = lean_array_get_size(x_33);
x_51 = lean_nat_dec_lt(x_27, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
x_43 = x_22;
goto block_49;
}
else
{
if (x_51 == 0)
{
lean_dec(x_50);
x_43 = x_22;
goto block_49;
}
else
{
size_t x_52; size_t x_53; uint8_t x_54; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_54 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_3, x_22, x_33, x_52, x_53);
if (x_54 == 0)
{
x_43 = x_22;
goto block_49;
}
else
{
lean_dec(x_19);
goto block_42;
}
}
}
block_42:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_33);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_33);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
if (lean_is_scalar(x_15)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_15;
}
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_9;
}
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_40);
return x_41;
}
block_49:
{
if (x_43 == 0)
{
lean_dec(x_19);
goto block_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_44 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_19);
lean_ctor_set(x_45, 1, x_33);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_12, 0);
x_56 = lean_ctor_get(x_12, 1);
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_string_utf8_byte_size(x_55);
x_60 = lean_nat_dec_lt(x_56, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_6);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_10, 1, x_61);
if (lean_is_scalar(x_15)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_15;
}
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_9;
}
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_83; lean_object* x_90; uint8_t x_91; 
lean_inc(x_56);
lean_inc_ref(x_55);
x_64 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_inc(x_64);
x_65 = lean_array_fset(x_58, x_5, x_64);
x_66 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_nat_mod(x_5, x_1);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
lean_ctor_set(x_10, 1, x_69);
lean_ctor_set(x_10, 0, x_67);
x_70 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_12, x_1, x_2, x_57, x_10);
lean_dec(x_12);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_string_utf8_next_fast(x_55, x_56);
lean_dec(x_56);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_55);
lean_ctor_set(x_76, 1, x_75);
x_90 = lean_array_get_size(x_73);
x_91 = lean_nat_dec_lt(x_66, x_90);
if (x_91 == 0)
{
lean_dec(x_90);
x_83 = x_60;
goto block_89;
}
else
{
if (x_91 == 0)
{
lean_dec(x_90);
x_83 = x_60;
goto block_89;
}
else
{
size_t x_92; size_t x_93; uint8_t x_94; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_90);
lean_dec(x_90);
x_94 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_3, x_60, x_73, x_92, x_93);
if (x_94 == 0)
{
x_83 = x_60;
goto block_89;
}
else
{
lean_dec(x_57);
goto block_82;
}
}
}
block_82:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_inc(x_73);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_73);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_15)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_15;
}
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_9;
}
lean_ctor_set(x_80, 0, x_4);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_80);
return x_81;
}
block_89:
{
if (x_83 == 0)
{
lean_dec(x_57);
goto block_82;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_84 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_57);
lean_ctor_set(x_85, 1, x_73);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_76);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_64);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_10, 0);
x_96 = lean_ctor_get(x_10, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_10);
x_97 = lean_ctor_get(x_8, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_98 = x_8;
} else {
 lean_dec_ref(x_8);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_string_utf8_byte_size(x_99);
x_105 = lean_nat_dec_lt(x_100, x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec_ref(x_6);
if (lean_is_scalar(x_103)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_103;
}
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_102);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_95);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_98)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_98;
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_9)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_9;
}
lean_ctor_set(x_109, 0, x_4);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_130; lean_object* x_137; uint8_t x_138; 
lean_inc(x_100);
lean_inc_ref(x_99);
x_110 = lean_nat_add(x_97, x_2);
lean_dec(x_97);
lean_inc(x_110);
x_111 = lean_array_fset(x_102, x_5, x_110);
x_112 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_6);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_nat_mod(x_5, x_1);
if (lean_is_scalar(x_103)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_103;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
x_117 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_95, x_1, x_2, x_101, x_116);
lean_dec(x_95);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_string_utf8_next_fast(x_99, x_100);
lean_dec(x_100);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_99);
lean_ctor_set(x_123, 1, x_122);
x_137 = lean_array_get_size(x_120);
x_138 = lean_nat_dec_lt(x_112, x_137);
if (x_138 == 0)
{
lean_dec(x_137);
x_130 = x_105;
goto block_136;
}
else
{
if (x_138 == 0)
{
lean_dec(x_137);
x_130 = x_105;
goto block_136;
}
else
{
size_t x_139; size_t x_140; uint8_t x_141; 
x_139 = 0;
x_140 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_141 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_3, x_105, x_120, x_139, x_140);
if (x_141 == 0)
{
x_130 = x_105;
goto block_136;
}
else
{
lean_dec(x_101);
goto block_129;
}
}
}
block_129:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_inc(x_120);
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_120);
if (lean_is_scalar(x_119)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_119;
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_98)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_98;
}
lean_ctor_set(x_126, 0, x_110);
lean_ctor_set(x_126, 1, x_125);
lean_inc(x_4);
if (lean_is_scalar(x_9)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_9;
}
lean_ctor_set(x_127, 0, x_4);
lean_ctor_set(x_127, 1, x_126);
x_128 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(x_4, x_2, x_5, x_1, x_6, x_3, x_127);
return x_128;
}
block_136:
{
if (x_130 == 0)
{
lean_dec(x_101);
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_121);
lean_dec(x_119);
lean_dec(x_98);
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
x_131 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_101);
lean_ctor_set(x_132, 1, x_120);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_110);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
return x_135;
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
x_15 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg(x_14, x_13, x_12);
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
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3(x_11, x_10, x_3, x_17, x_12, x_2, x_21);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Data_Range_Basic_0__Std_Range_forIn_x27_loop___at___Lean_EditDistance_levenshtein_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_EditDistance_levenshtein_spec__2(x_1, x_6, x_3, x_7, x_8);
lean_dec_ref(x_3);
lean_dec(x_1);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at_____private_Init_While_0__Lean_Loop_forIn_loop___at___Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
