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
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_57; 
x_7 = lean_ctor_get(x_6, 1);
x_8 = lean_ctor_get(x_6, 0);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
x_9 = x_6;
x_10 = x_57;
goto block_56;
}
else
{
lean_inc(x_7);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_55; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
x_13 = x_7;
x_14 = x_55;
goto block_54;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_string_utf8_byte_size(x_1);
x_16 = lean_nat_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_31; lean_object* x_32; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_42; uint32_t x_43; uint8_t x_44; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_mod(x_17, x_2);
x_19 = l_Fin_add(x_2, x_11, x_18);
lean_dec(x_18);
x_35 = lean_array_fget_borrowed(x_3, x_19);
x_36 = lean_nat_add(x_35, x_17);
x_37 = lean_array_fget_borrowed(x_12, x_11);
x_38 = lean_nat_add(x_37, x_17);
x_42 = lean_string_utf8_get_fast(x_5, x_4);
x_43 = lean_string_utf8_get_fast(x_1, x_8);
x_44 = lean_uint32_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_fget_borrowed(x_3, x_11);
lean_dec(x_11);
x_46 = lean_nat_add(x_45, x_17);
x_39 = x_46;
goto block_41;
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget_borrowed(x_3, x_11);
lean_dec(x_11);
lean_inc(x_47);
x_39 = x_47;
goto block_41;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_array_fset(x_12, x_19, x_20);
x_22 = lean_string_utf8_next_fast(x_1, x_8);
lean_dec(x_8);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_21);
lean_ctor_set(x_13, 0, x_19);
x_23 = x_13;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_21);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_23);
lean_ctor_set(x_9, 0, x_22);
x_24 = x_9;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
x_24 = x_27;
goto block_26;
}
block_26:
{
x_6 = x_24;
goto _start;
}
}
}
block_34:
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_32, x_31);
if (x_33 == 0)
{
lean_dec(x_32);
x_20 = x_31;
goto block_30;
}
else
{
lean_dec(x_31);
x_20 = x_32;
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
else
{
lean_object* x_48; 
if (x_14 == 0)
{
x_48 = x_13;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_11);
lean_ctor_set(x_53, 1, x_12);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_48);
x_49 = x_9;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_48);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_94; 
x_6 = lean_ctor_get(x_5, 1);
x_94 = !lean_is_exclusive(x_5);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_5, 0);
lean_dec(x_95);
x_7 = x_5;
x_8 = x_94;
goto block_93;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_91; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_6, 1);
lean_dec(x_92);
x_12 = x_6;
x_13 = x_91;
goto block_90;
}
else
{
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_88; 
x_14 = lean_ctor_get(x_9, 0);
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_9, 1);
lean_dec(x_89);
x_15 = x_9;
x_16 = x_88;
goto block_87;
}
else
{
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_86; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
x_86 = !lean_is_exclusive(x_10);
if (x_86 == 0)
{
x_19 = x_10;
x_20 = x_86;
goto block_85;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_box(0);
x_22 = lean_string_utf8_byte_size(x_1);
x_23 = lean_nat_dec_eq(x_14, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
lean_inc(x_26);
x_27 = lean_array_fset(x_18, x_25, x_26);
x_28 = lean_nat_mod(x_25, x_2);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_28);
x_29 = x_19;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_28);
lean_ctor_set(x_72, 1, x_27);
x_29 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_30; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_29);
lean_ctor_set(x_15, 0, x_25);
x_30 = x_15;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_25);
lean_ctor_set(x_70, 1, x_29);
x_30 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_67; 
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_3, x_2, x_17, x_14, x_1, x_30);
x_32 = lean_ctor_get(x_31, 1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_31, 0);
lean_dec(x_68);
x_33 = x_31;
x_34 = x_67;
goto block_66;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_64; 
x_35 = lean_ctor_get(x_32, 1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_32, 0);
lean_dec(x_65);
x_36 = x_32;
x_37 = x_64;
goto block_63;
}
else
{
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_38; lean_object* x_53; uint8_t x_54; 
x_38 = lean_string_utf8_next_fast(x_1, x_14);
lean_dec(x_14);
x_53 = lean_array_get_size(x_35);
x_54 = lean_nat_dec_lt(x_25, x_53);
if (x_54 == 0)
{
goto block_52;
}
else
{
if (x_54 == 0)
{
goto block_52;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_53);
x_57 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_35, x_55, x_56);
if (x_57 == 0)
{
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_del_object(x_36);
lean_del_object(x_33);
lean_dec(x_17);
lean_del_object(x_12);
lean_del_object(x_7);
lean_inc(x_35);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_35);
lean_ctor_set(x_58, 1, x_35);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_21);
lean_ctor_set(x_61, 1, x_60);
x_5 = x_61;
goto _start;
}
}
}
block_52:
{
lean_object* x_39; lean_object* x_40; 
x_39 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_17);
x_40 = x_36;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_35);
x_40 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_41; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_40);
lean_ctor_set(x_33, 0, x_38);
x_41 = x_33;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_40);
x_41 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_42; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_41);
lean_ctor_set(x_12, 0, x_26);
x_42 = x_12;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_41);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_42);
lean_ctor_set(x_7, 0, x_39);
x_43 = x_7;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_73; 
if (x_20 == 0)
{
x_73 = x_19;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_17);
lean_ctor_set(x_84, 1, x_18);
x_73 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_74; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_73);
x_74 = x_15;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_14);
lean_ctor_set(x_82, 1, x_73);
x_74 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_75; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_74);
x_75 = x_12;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_11);
lean_ctor_set(x_80, 1, x_74);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_75);
lean_ctor_set(x_7, 0, x_21);
x_76 = x_7;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_21);
lean_ctor_set(x_78, 1, x_75);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
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
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_94; 
x_6 = lean_ctor_get(x_5, 1);
x_94 = !lean_is_exclusive(x_5);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_5, 0);
lean_dec(x_95);
x_7 = x_5;
x_8 = x_94;
goto block_93;
}
else
{
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_91; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_6, 1);
lean_dec(x_92);
x_12 = x_6;
x_13 = x_91;
goto block_90;
}
else
{
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_88; 
x_14 = lean_ctor_get(x_9, 0);
x_88 = !lean_is_exclusive(x_9);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_9, 1);
lean_dec(x_89);
x_15 = x_9;
x_16 = x_88;
goto block_87;
}
else
{
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_86; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
x_86 = !lean_is_exclusive(x_10);
if (x_86 == 0)
{
x_19 = x_10;
x_20 = x_86;
goto block_85;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_box(0);
x_20 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_box(0);
x_22 = lean_string_utf8_byte_size(x_3);
x_23 = lean_nat_dec_eq(x_14, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_add(x_11, x_24);
lean_dec(x_11);
lean_inc(x_26);
x_27 = lean_array_fset(x_18, x_25, x_26);
x_28 = lean_nat_mod(x_25, x_2);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_27);
lean_ctor_set(x_19, 0, x_28);
x_29 = x_19;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_28);
lean_ctor_set(x_72, 1, x_27);
x_29 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_30; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_29);
lean_ctor_set(x_15, 0, x_25);
x_30 = x_15;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_25);
lean_ctor_set(x_70, 1, x_29);
x_30 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_67; 
x_31 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__1(x_1, x_2, x_17, x_14, x_3, x_30);
x_32 = lean_ctor_get(x_31, 1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_31, 0);
lean_dec(x_68);
x_33 = x_31;
x_34 = x_67;
goto block_66;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_64; 
x_35 = lean_ctor_get(x_32, 1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_32, 0);
lean_dec(x_65);
x_36 = x_32;
x_37 = x_64;
goto block_63;
}
else
{
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_box(0);
x_37 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_38; lean_object* x_53; uint8_t x_54; 
x_38 = lean_string_utf8_next_fast(x_3, x_14);
lean_dec(x_14);
x_53 = lean_array_get_size(x_35);
x_54 = lean_nat_dec_lt(x_25, x_53);
if (x_54 == 0)
{
goto block_52;
}
else
{
if (x_54 == 0)
{
goto block_52;
}
else
{
size_t x_55; size_t x_56; uint8_t x_57; 
x_55 = 0;
x_56 = lean_usize_of_nat(x_53);
x_57 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_EditDistance_levenshtein_spec__2(x_4, x_35, x_55, x_56);
if (x_57 == 0)
{
goto block_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_del_object(x_36);
lean_del_object(x_33);
lean_dec(x_17);
lean_del_object(x_12);
lean_del_object(x_7);
lean_inc(x_35);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_35);
lean_ctor_set(x_58, 1, x_35);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_26);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_21);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3(x_3, x_2, x_1, x_4, x_61);
return x_62;
}
}
}
block_52:
{
lean_object* x_39; lean_object* x_40; 
x_39 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_EditDistance_levenshtein_spec__3_spec__3___closed__0));
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_17);
x_40 = x_36;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_17);
lean_ctor_set(x_51, 1, x_35);
x_40 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_41; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_40);
lean_ctor_set(x_33, 0, x_38);
x_41 = x_33;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_40);
x_41 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_42; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_41);
lean_ctor_set(x_12, 0, x_26);
x_42 = x_12;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_26);
lean_ctor_set(x_47, 1, x_41);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_42);
lean_ctor_set(x_7, 0, x_39);
x_43 = x_7;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_73; 
if (x_20 == 0)
{
x_73 = x_19;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_17);
lean_ctor_set(x_84, 1, x_18);
x_73 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_74; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_73);
x_74 = x_15;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_14);
lean_ctor_set(x_82, 1, x_73);
x_74 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_75; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_74);
x_75 = x_12;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_11);
lean_ctor_set(x_80, 1, x_74);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_75);
lean_ctor_set(x_7, 0, x_21);
x_76 = x_7;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_21);
lean_ctor_set(x_78, 1, x_75);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
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
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_EditDistance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Init_Data_String_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_EditDistance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_EditDistance(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_EditDistance(builtin);
}
#ifdef __cplusplus
}
#endif
