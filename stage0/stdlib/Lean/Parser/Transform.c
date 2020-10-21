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
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_ULift_HasRepr___rarg___closed__2;
lean_object* l_Lean_Syntax_removeParen_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Syntax_manyToSepBy_match__2(lean_object*);
lean_object* l_Lean_Syntax_removeParen(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l_Lean_Syntax_manyToSepBy_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Syntax_removeParen_match__1(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__11___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_5);
x_10 = l_Lean_Syntax_getTailInfo(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
x_13 = l_Lean_SourceInfo_inhabited___closed__1;
lean_inc(x_1);
x_14 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_array_push(x_5, x_14);
x_16 = lean_array_push(x_15, x_8);
x_4 = x_12;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_SourceInfo_inhabited___closed__1;
x_20 = l_Lean_Syntax_setTailInfo(x_9, x_19);
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_sub(x_21, x_11);
lean_dec(x_21);
x_23 = lean_array_set(x_5, x_22, x_20);
lean_dec(x_22);
lean_inc(x_1);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_1);
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_array_push(x_25, x_8);
x_4 = x_12;
x_5 = x_26;
goto _start;
}
}
}
}
lean_object* l_Lean_Syntax_manyToSepBy(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Syntax_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_mkOptionalNode___closed__2;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_4, x_4, x_10, x_9);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_11);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Syntax_inhabited;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_13, x_15);
x_17 = l_Lean_mkOptionalNode___closed__2;
x_18 = lean_array_push(x_17, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_13, x_13, x_19, x_18);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
x_26 = l_ULift_HasRepr___rarg___closed__2;
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
x_4 = l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_inc(x_3);
x_9 = l_Lean_Syntax_inhabited;
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_array_get(x_9, x_3, x_10);
lean_inc(x_11);
x_97 = l_Lean_Syntax_getNumArgs(x_11);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = 1;
x_12 = x_100;
goto block_96;
}
else
{
uint8_t x_101; 
x_101 = 0;
x_12 = x_101;
goto block_96;
}
block_96:
{
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Syntax_getArg(x_11, x_10);
x_14 = l_Lean_Syntax_isNone(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_11, x_15);
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_array_get(x_9, x_3, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Syntax_getTailInfo(x_16);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_19, 2);
lean_inc(x_24);
lean_dec(x_19);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
return x_1;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_ULift_HasRepr___rarg___closed__2;
x_27 = lean_string_dec_eq(x_20, x_26);
lean_dec(x_20);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_16);
return x_1;
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_dec(x_25);
lean_dec(x_16);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_28, 0);
lean_dec(x_34);
if (lean_obj_tag(x_32) == 0)
{
lean_free_object(x_28);
lean_dec(x_25);
lean_dec(x_16);
return x_1;
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 2);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_string_utf8_extract(x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_41 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__11___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = !lean_is_exclusive(x_25);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
x_46 = lean_ctor_get(x_25, 2);
x_47 = lean_string_utf8_extract(x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_48 = lean_string_append(x_42, x_47);
lean_dec(x_47);
x_49 = lean_string_utf8_byte_size(x_48);
lean_ctor_set(x_25, 2, x_49);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 0, x_48);
lean_ctor_set(x_32, 0, x_25);
x_50 = l_Lean_Syntax_setTailInfo(x_16, x_28);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
x_53 = lean_ctor_get(x_25, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
x_54 = lean_string_utf8_extract(x_51, x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_55 = lean_string_append(x_42, x_54);
lean_dec(x_54);
x_56 = lean_string_utf8_byte_size(x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_15);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_32, 0, x_57);
x_58 = l_Lean_Syntax_setTailInfo(x_16, x_28);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_59 = lean_ctor_get(x_32, 0);
lean_inc(x_59);
lean_dec(x_32);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_string_utf8_extract(x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_64 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__11___closed__3;
x_65 = lean_string_append(x_63, x_64);
x_66 = lean_ctor_get(x_25, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_25, 2);
lean_inc(x_68);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_69 = x_25;
} else {
 lean_dec_ref(x_25);
 x_69 = lean_box(0);
}
x_70 = lean_string_utf8_extract(x_66, x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_71 = lean_string_append(x_65, x_70);
lean_dec(x_70);
x_72 = lean_string_utf8_byte_size(x_71);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(0, 3, 0);
} else {
 x_73 = x_69;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_15);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_28, 2, x_74);
x_75 = l_Lean_Syntax_setTailInfo(x_16, x_28);
return x_75;
}
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_28, 2);
lean_inc(x_76);
lean_dec(x_28);
if (lean_obj_tag(x_76) == 0)
{
lean_dec(x_25);
lean_dec(x_16);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 2);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_string_utf8_extract(x_79, x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
x_83 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__11___closed__3;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_ctor_get(x_25, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_25, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_25, 2);
lean_inc(x_87);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_88 = x_25;
} else {
 lean_dec_ref(x_25);
 x_88 = lean_box(0);
}
x_89 = lean_string_utf8_extract(x_85, x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_90 = lean_string_append(x_84, x_89);
lean_dec(x_89);
x_91 = lean_string_utf8_byte_size(x_90);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 3, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_15);
lean_ctor_set(x_92, 2, x_91);
if (lean_is_scalar(x_78)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_78;
}
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_29);
lean_ctor_set(x_94, 1, x_30);
lean_ctor_set(x_94, 2, x_93);
x_95 = l_Lean_Syntax_setTailInfo(x_16, x_94);
return x_95;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_16);
return x_1;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_16);
return x_1;
}
}
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
return x_1;
}
}
else
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
return x_1;
}
}
else
{
lean_dec(x_18);
lean_dec(x_16);
return x_1;
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_3);
return x_1;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
lean_dec(x_1);
lean_inc(x_3);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_2);
lean_ctor_set(x_102, 1, x_3);
x_103 = l_Lean_Syntax_inhabited;
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_array_get(x_103, x_3, x_104);
lean_inc(x_105);
x_147 = l_Lean_Syntax_getNumArgs(x_105);
x_148 = lean_unsigned_to_nat(2u);
x_149 = lean_nat_dec_eq(x_147, x_148);
lean_dec(x_147);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = 1;
x_106 = x_150;
goto block_146;
}
else
{
uint8_t x_151; 
x_151 = 0;
x_106 = x_151;
goto block_146;
}
block_146:
{
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = l_Lean_Syntax_getArg(x_105, x_104);
x_108 = l_Lean_Syntax_isNone(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_dec(x_105);
lean_dec(x_3);
return x_102;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_Syntax_getArg(x_105, x_109);
lean_dec(x_105);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_array_get(x_103, x_3, x_111);
lean_dec(x_3);
if (lean_obj_tag(x_112) == 2)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Syntax_getTailInfo(x_110);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_113, 2);
lean_inc(x_118);
lean_dec(x_113);
if (lean_obj_tag(x_118) == 0)
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_110);
return x_102;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
x_120 = l_ULift_HasRepr___rarg___closed__2;
x_121 = lean_string_dec_eq(x_114, x_120);
lean_dec(x_114);
if (x_121 == 0)
{
lean_dec(x_119);
lean_dec(x_115);
lean_dec(x_110);
return x_102;
}
else
{
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_119);
lean_dec(x_110);
return x_102;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_115, 0);
lean_inc(x_122);
lean_dec(x_115);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 2);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
if (lean_obj_tag(x_125) == 0)
{
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_110);
return x_102;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_102);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 2);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_string_utf8_extract(x_129, x_130, x_131);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
x_133 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__11___closed__3;
x_134 = lean_string_append(x_132, x_133);
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_119, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 2);
lean_inc(x_137);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 lean_ctor_release(x_119, 2);
 x_138 = x_119;
} else {
 lean_dec_ref(x_119);
 x_138 = lean_box(0);
}
x_139 = lean_string_utf8_extract(x_135, x_136, x_137);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
x_140 = lean_string_append(x_134, x_139);
lean_dec(x_139);
x_141 = lean_string_utf8_byte_size(x_140);
if (lean_is_scalar(x_138)) {
 x_142 = lean_alloc_ctor(0, 3, 0);
} else {
 x_142 = x_138;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_109);
lean_ctor_set(x_142, 2, x_141);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_142);
if (lean_is_scalar(x_126)) {
 x_144 = lean_alloc_ctor(0, 3, 0);
} else {
 x_144 = x_126;
}
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_124);
lean_ctor_set(x_144, 2, x_143);
x_145 = l_Lean_Syntax_setTailInfo(x_110, x_144);
return x_145;
}
}
else
{
lean_dec(x_124);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_110);
return x_102;
}
}
else
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_110);
return x_102;
}
}
}
}
}
else
{
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
return x_102;
}
}
else
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_110);
return x_102;
}
}
else
{
lean_dec(x_112);
lean_dec(x_110);
return x_102;
}
}
}
else
{
lean_dec(x_105);
lean_dec(x_3);
return x_102;
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
