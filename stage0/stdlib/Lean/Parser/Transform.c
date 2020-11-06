// Lean compiler output
// Module: Lean.Parser.Transform
// Imports: Init Lean.Parser.Basic
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__9;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__11___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__1(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Init_Data_Repr___instance__7___rarg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__2(lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__8___closed__1;
lean_object* l_Lean_Syntax_removeParen(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Syntax_removeParen_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_manyToSepBy_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_manyToSepBy_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_manyToSepBy_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l_Lean_Syntax_manyToSepBy_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_manyToSepBy_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_nat_dec_le(x_7, x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = l_Lean_Init_LeanInit___instance__9;
x_14 = lean_array_get(x_13, x_2, x_5);
x_15 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_6);
x_16 = l_Lean_Syntax_getTailInfo(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_17 = l_Lean_Init_LeanInit___instance__8___closed__1;
lean_inc(x_1);
x_18 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_array_push(x_6, x_18);
x_20 = lean_array_push(x_19, x_14);
x_21 = lean_ctor_get(x_3, 2);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_22;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_array_get_size(x_6);
x_26 = lean_nat_sub(x_25, x_11);
lean_dec(x_25);
x_27 = lean_array_set(x_6, x_26, x_15);
lean_dec(x_26);
lean_inc(x_1);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_1);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_array_push(x_29, x_14);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_4 = x_12;
x_5 = x_32;
x_6 = x_30;
goto _start;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
}
lean_object* l_Lean_Syntax_manyToSepBy(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_5, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = l_Lean_Init_LeanInit___instance__9;
x_12 = lean_array_get(x_11, x_4, x_6);
x_13 = l_Lean_mkOptionalNode___closed__2;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_4, x_16, x_5, x_15, x_14);
lean_dec(x_16);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_18 = l_Lean_Init_LeanInit___instance__9;
x_19 = lean_array_get(x_18, x_4, x_6);
x_20 = l_Lean_mkOptionalNode___closed__2;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_unsigned_to_nat(1u);
lean_inc(x_5);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_4, x_23, x_5, x_22, x_21);
lean_dec(x_23);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Range_forIn_loop___at_Lean_Syntax_manyToSepBy___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Syntax_removeParen_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_3);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_5, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
lean_ctor_set(x_5, 0, x_8);
x_15 = lean_apply_2(x_4, x_1, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
lean_ctor_set(x_5, 0, x_8);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_2(x_4, x_17, x_2);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_20 = x_1;
} else {
 lean_dec_ref(x_1);
 x_20 = lean_box(0);
}
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_7);
lean_ctor_set(x_21, 2, x_8);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(2, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_apply_2(x_4, x_22, x_2);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
x_26 = l_Init_Data_Repr___instance__7___rarg___closed__2;
x_27 = lean_string_dec_eq(x_24, x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_28 = lean_apply_2(x_4, x_1, x_2);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_26);
x_32 = lean_apply_2(x_4, x_1, x_2);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_5, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_5, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_5, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_2, 0);
lean_dec(x_41);
x_42 = lean_ctor_get(x_33, 2);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_33, 2);
lean_dec(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_33, 0);
lean_dec(x_46);
lean_ctor_set(x_33, 2, x_8);
lean_ctor_set(x_33, 0, x_42);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_33);
lean_ctor_set(x_5, 2, x_42);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_42);
lean_ctor_set(x_2, 0, x_5);
x_47 = lean_apply_2(x_4, x_1, x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_39);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set(x_5, 2, x_42);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_42);
lean_ctor_set(x_2, 0, x_5);
x_49 = lean_apply_2(x_4, x_1, x_2);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_free_object(x_2);
lean_free_object(x_5);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_4);
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = lean_apply_3(x_3, x_25, x_33, x_50);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_2);
x_52 = lean_ctor_get(x_33, 2);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_25);
lean_dec(x_3);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_53 = x_33;
} else {
 lean_dec_ref(x_33);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_39);
lean_ctor_set(x_54, 2, x_8);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_54);
lean_ctor_set(x_5, 2, x_52);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_52);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_5);
x_56 = lean_apply_2(x_4, x_1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_free_object(x_5);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_4);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_apply_3(x_3, x_25, x_33, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_39);
lean_free_object(x_5);
lean_dec(x_25);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_33);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_33, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_33, 1);
lean_dec(x_61);
x_62 = lean_ctor_get(x_33, 0);
lean_dec(x_62);
lean_ctor_set(x_33, 2, x_8);
lean_ctor_set(x_33, 1, x_7);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_33);
x_63 = lean_apply_2(x_4, x_1, x_2);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_7);
lean_ctor_set(x_64, 2, x_8);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_64);
x_65 = lean_apply_2(x_4, x_1, x_2);
return x_65;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_5);
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_67 = x_2;
} else {
 lean_dec_ref(x_2);
 x_67 = lean_box(0);
}
x_68 = lean_ctor_get(x_33, 2);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_25);
lean_dec(x_3);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_69 = x_33;
} else {
 lean_dec_ref(x_33);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_8);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_70);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_66);
lean_ctor_set(x_71, 2, x_68);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_apply_2(x_4, x_1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_67);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_4);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
lean_dec(x_68);
x_75 = lean_apply_3(x_3, x_25, x_33, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
lean_dec(x_25);
lean_dec(x_3);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_76 = x_33;
} else {
 lean_dec_ref(x_33);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 3, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_34);
lean_ctor_set(x_77, 1, x_7);
lean_ctor_set(x_77, 2, x_8);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_77);
x_78 = lean_apply_2(x_4, x_1, x_2);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_26);
x_79 = lean_apply_2(x_4, x_1, x_2);
return x_79;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
x_80 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_26);
x_81 = lean_apply_2(x_4, x_80, x_2);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_84 = x_5;
} else {
 lean_dec_ref(x_5);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_86 = x_2;
} else {
 lean_dec_ref(x_2);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_82, 2);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_25);
lean_dec(x_3);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 x_88 = x_82;
} else {
 lean_dec_ref(x_82);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_8);
x_90 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_26);
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 3, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_85);
lean_ctor_set(x_91, 2, x_87);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_apply_2(x_4, x_90, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_4);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
lean_dec(x_87);
x_95 = lean_apply_3(x_3, x_25, x_82, x_94);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_25);
lean_dec(x_3);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 lean_ctor_release(x_82, 2);
 x_96 = x_82;
} else {
 lean_dec_ref(x_82);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 3, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_83);
lean_ctor_set(x_97, 1, x_7);
lean_ctor_set(x_97, 2, x_8);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_26);
x_99 = lean_apply_2(x_4, x_98, x_2);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_3);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_26);
x_101 = lean_apply_2(x_4, x_100, x_2);
return x_101;
}
}
}
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_102 = lean_apply_2(x_4, x_1, x_2);
return x_102;
}
}
else
{
lean_object* x_103; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_103 = lean_apply_2(x_4, x_1, x_2);
return x_103;
}
}
else
{
lean_object* x_104; 
lean_dec(x_3);
x_104 = lean_apply_2(x_4, x_1, x_2);
return x_104;
}
}
}
lean_object* l_Lean_Syntax_removeParen_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Syntax_removeParen_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Syntax_removeParen(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = l_Lean_myMacro____x40_Lean_Message___hyg_1877____closed__3;
x_5 = lean_name_eq(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_inc(x_3);
x_9 = l_Lean_Init_LeanInit___instance__9;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_3, x_10);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getNumArgs(x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Syntax_getArg(x_11, x_10);
x_16 = l_Lean_Syntax_isNone(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_11);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_11, x_17);
lean_dec(x_11);
x_19 = lean_array_get(x_9, x_3, x_13);
lean_dec(x_3);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getTailInfo(x_18);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_20, 2);
lean_inc(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Init_Data_Repr___instance__7___rarg___closed__2;
x_28 = lean_string_dec_eq(x_21, x_27);
lean_dec(x_21);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
return x_1;
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_26);
lean_dec(x_18);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
if (lean_obj_tag(x_33) == 0)
{
lean_free_object(x_29);
lean_dec(x_26);
lean_dec(x_18);
return x_1;
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 2);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_string_utf8_extract(x_38, x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__11___closed__3;
x_43 = lean_string_append(x_41, x_42);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
x_47 = lean_ctor_get(x_26, 2);
x_48 = lean_string_utf8_extract(x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_49 = lean_string_append(x_43, x_48);
lean_dec(x_48);
x_50 = lean_string_utf8_byte_size(x_49);
lean_ctor_set(x_26, 2, x_50);
lean_ctor_set(x_26, 1, x_17);
lean_ctor_set(x_26, 0, x_49);
lean_ctor_set(x_33, 0, x_26);
x_51 = l_Lean_Syntax_setTailInfo(x_18, x_29);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
x_54 = lean_ctor_get(x_26, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_55 = lean_string_utf8_extract(x_52, x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_56 = lean_string_append(x_43, x_55);
lean_dec(x_55);
x_57 = lean_string_utf8_byte_size(x_56);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_17);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_33, 0, x_58);
x_59 = l_Lean_Syntax_setTailInfo(x_18, x_29);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_60 = lean_ctor_get(x_33, 0);
lean_inc(x_60);
lean_dec(x_33);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_string_utf8_extract(x_61, x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__11___closed__3;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_ctor_get(x_26, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_26, 2);
lean_inc(x_69);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_70 = x_26;
} else {
 lean_dec_ref(x_26);
 x_70 = lean_box(0);
}
x_71 = lean_string_utf8_extract(x_67, x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
x_72 = lean_string_append(x_66, x_71);
lean_dec(x_71);
x_73 = lean_string_utf8_byte_size(x_72);
if (lean_is_scalar(x_70)) {
 x_74 = lean_alloc_ctor(0, 3, 0);
} else {
 x_74 = x_70;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_17);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_29, 2, x_75);
x_76 = l_Lean_Syntax_setTailInfo(x_18, x_29);
return x_76;
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_29, 2);
lean_inc(x_77);
lean_dec(x_29);
if (lean_obj_tag(x_77) == 0)
{
lean_dec(x_26);
lean_dec(x_18);
return x_1;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 2);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_string_utf8_extract(x_80, x_81, x_82);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
x_84 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__11___closed__3;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_ctor_get(x_26, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_26, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_26, 2);
lean_inc(x_88);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_89 = x_26;
} else {
 lean_dec_ref(x_26);
 x_89 = lean_box(0);
}
x_90 = lean_string_utf8_extract(x_86, x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
x_91 = lean_string_append(x_85, x_90);
lean_dec(x_90);
x_92 = lean_string_utf8_byte_size(x_91);
if (lean_is_scalar(x_89)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_89;
}
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_17);
lean_ctor_set(x_93, 2, x_92);
if (lean_is_scalar(x_79)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_79;
}
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_30);
lean_ctor_set(x_95, 1, x_31);
lean_ctor_set(x_95, 2, x_94);
x_96 = l_Lean_Syntax_setTailInfo(x_18, x_95);
return x_96;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_18);
return x_1;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_18);
return x_1;
}
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
return x_1;
}
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
return x_1;
}
}
else
{
lean_dec(x_19);
lean_dec(x_18);
return x_1;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_1);
lean_inc(x_3);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_3);
x_98 = l_Lean_Init_LeanInit___instance__9;
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_array_get(x_98, x_3, x_99);
lean_inc(x_100);
x_101 = l_Lean_Syntax_getNumArgs(x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_dec_eq(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_dec(x_100);
lean_dec(x_3);
return x_97;
}
else
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Syntax_getArg(x_100, x_99);
x_105 = l_Lean_Syntax_isNone(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_dec(x_100);
lean_dec(x_3);
return x_97;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = l_Lean_Syntax_getArg(x_100, x_106);
lean_dec(x_100);
x_108 = lean_array_get(x_98, x_3, x_102);
lean_dec(x_3);
if (lean_obj_tag(x_108) == 2)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Syntax_getTailInfo(x_107);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_109, 2);
lean_inc(x_114);
lean_dec(x_109);
if (lean_obj_tag(x_114) == 0)
{
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_107);
return x_97;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Init_Data_Repr___instance__7___rarg___closed__2;
x_117 = lean_string_dec_eq(x_110, x_116);
lean_dec(x_110);
if (x_117 == 0)
{
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_107);
return x_97;
}
else
{
if (lean_obj_tag(x_111) == 0)
{
lean_dec(x_115);
lean_dec(x_107);
return x_97;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_111, 0);
lean_inc(x_118);
lean_dec(x_111);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_118, 2);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
if (lean_obj_tag(x_121) == 0)
{
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_107);
return x_97;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_97);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 2);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_string_utf8_extract(x_125, x_126, x_127);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
x_129 = l_Array_foldlMUnsafe_fold___at_Lean_Environment_displayStats___spec__11___closed__3;
x_130 = lean_string_append(x_128, x_129);
x_131 = lean_ctor_get(x_115, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_115, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_115, 2);
lean_inc(x_133);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 x_134 = x_115;
} else {
 lean_dec_ref(x_115);
 x_134 = lean_box(0);
}
x_135 = lean_string_utf8_extract(x_131, x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
x_136 = lean_string_append(x_130, x_135);
lean_dec(x_135);
x_137 = lean_string_utf8_byte_size(x_136);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 3, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_106);
lean_ctor_set(x_138, 2, x_137);
if (lean_is_scalar(x_124)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_124;
}
lean_ctor_set(x_139, 0, x_138);
if (lean_is_scalar(x_122)) {
 x_140 = lean_alloc_ctor(0, 3, 0);
} else {
 x_140 = x_122;
}
lean_ctor_set(x_140, 0, x_119);
lean_ctor_set(x_140, 1, x_120);
lean_ctor_set(x_140, 2, x_139);
x_141 = l_Lean_Syntax_setTailInfo(x_107, x_140);
return x_141;
}
}
else
{
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_107);
return x_97;
}
}
else
{
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_107);
return x_97;
}
}
}
}
}
else
{
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
return x_97;
}
}
else
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
return x_97;
}
}
else
{
lean_dec(x_108);
lean_dec(x_107);
return x_97;
}
}
}
}
}
}
else
{
return x_1;
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Parser_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Parser_Transform(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
