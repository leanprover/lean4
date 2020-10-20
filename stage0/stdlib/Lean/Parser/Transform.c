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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Syntax_removeParen(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getTailInfo(lean_object*);
extern lean_object* l_myMacro____x40_Init_Data_ToString_Macro___hyg_39____closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_inc(x_3);
x_9 = l_Lean_Syntax_inhabited;
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
x_23 = lean_ctor_get(x_20, 2);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_18);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_ULift_HasRepr___rarg___closed__2;
x_26 = lean_string_dec_eq(x_21, x_25);
lean_dec(x_21);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_18);
return x_1;
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_24);
lean_dec(x_18);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 2);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_18);
return x_1;
}
else
{
uint8_t x_29; 
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_27, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_string_utf8_extract(x_33, x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_37 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_38 = lean_string_append(x_36, x_37);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
x_42 = lean_ctor_get(x_24, 2);
x_43 = lean_string_utf8_extract(x_40, x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
x_44 = lean_string_append(x_38, x_43);
lean_dec(x_43);
x_45 = lean_string_utf8_byte_size(x_44);
lean_ctor_set(x_24, 2, x_45);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 0, x_44);
lean_ctor_set(x_28, 0, x_24);
x_46 = l_Lean_Syntax_setTailInfo(x_18, x_27);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
x_49 = lean_ctor_get(x_24, 2);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_50 = lean_string_utf8_extract(x_47, x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
x_51 = lean_string_append(x_38, x_50);
lean_dec(x_50);
x_52 = lean_string_utf8_byte_size(x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_17);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_28, 0, x_53);
x_54 = l_Lean_Syntax_setTailInfo(x_18, x_27);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_55 = lean_ctor_get(x_28, 0);
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_55, 2);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_string_utf8_extract(x_58, x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_62 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_ctor_get(x_24, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_24, 2);
lean_inc(x_66);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_67 = x_24;
} else {
 lean_dec_ref(x_24);
 x_67 = lean_box(0);
}
x_68 = lean_string_utf8_extract(x_64, x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
x_69 = lean_string_append(x_63, x_68);
lean_dec(x_68);
x_70 = lean_string_utf8_byte_size(x_69);
if (lean_is_scalar(x_67)) {
 x_71 = lean_alloc_ctor(0, 3, 0);
} else {
 x_71 = x_67;
}
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_17);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_28, 0, x_71);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_56);
lean_ctor_set(x_72, 1, x_57);
lean_ctor_set(x_72, 2, x_28);
x_73 = l_Lean_Syntax_setTailInfo(x_18, x_72);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_74 = lean_ctor_get(x_28, 0);
lean_inc(x_74);
lean_dec(x_28);
x_75 = lean_ctor_get(x_27, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 lean_ctor_release(x_27, 2);
 x_77 = x_27;
} else {
 lean_dec_ref(x_27);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 2);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_string_utf8_extract(x_78, x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_82 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_ctor_get(x_24, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_24, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_24, 2);
lean_inc(x_86);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_87 = x_24;
} else {
 lean_dec_ref(x_24);
 x_87 = lean_box(0);
}
x_88 = lean_string_utf8_extract(x_84, x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_89 = lean_string_append(x_83, x_88);
lean_dec(x_88);
x_90 = lean_string_utf8_byte_size(x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(0, 3, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_17);
lean_ctor_set(x_91, 2, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_77)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_77;
}
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_76);
lean_ctor_set(x_93, 2, x_92);
x_94 = l_Lean_Syntax_setTailInfo(x_18, x_93);
return x_94;
}
}
}
}
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
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_1);
lean_inc(x_3);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_3);
x_96 = l_Lean_Syntax_inhabited;
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_array_get(x_96, x_3, x_97);
lean_inc(x_98);
x_99 = l_Lean_Syntax_getNumArgs(x_98);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_nat_dec_eq(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_dec(x_98);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Syntax_getArg(x_98, x_97);
x_103 = l_Lean_Syntax_isNone(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_dec(x_98);
lean_dec(x_3);
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Syntax_getArg(x_98, x_104);
lean_dec(x_98);
x_106 = lean_array_get(x_96, x_3, x_100);
lean_dec(x_3);
if (lean_obj_tag(x_106) == 2)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Syntax_getTailInfo(x_105);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
lean_dec(x_107);
if (lean_obj_tag(x_110) == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_105);
return x_95;
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_ULift_HasRepr___rarg___closed__2;
x_113 = lean_string_dec_eq(x_108, x_112);
lean_dec(x_108);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_105);
return x_95;
}
else
{
if (lean_obj_tag(x_109) == 0)
{
lean_dec(x_111);
lean_dec(x_105);
return x_95;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_109, 0);
lean_inc(x_114);
lean_dec(x_109);
x_115 = lean_ctor_get(x_114, 2);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_dec(x_114);
lean_dec(x_111);
lean_dec(x_105);
return x_95;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_95);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 x_120 = x_114;
} else {
 lean_dec_ref(x_114);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 2);
lean_inc(x_123);
lean_dec(x_116);
x_124 = lean_string_utf8_extract(x_121, x_122, x_123);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
x_125 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_ctor_get(x_111, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_111, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 2);
lean_inc(x_129);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 x_130 = x_111;
} else {
 lean_dec_ref(x_111);
 x_130 = lean_box(0);
}
x_131 = lean_string_utf8_extract(x_127, x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
x_132 = lean_string_append(x_126, x_131);
lean_dec(x_131);
x_133 = lean_string_utf8_byte_size(x_132);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_104);
lean_ctor_set(x_134, 2, x_133);
if (lean_is_scalar(x_117)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_117;
}
lean_ctor_set(x_135, 0, x_134);
if (lean_is_scalar(x_120)) {
 x_136 = lean_alloc_ctor(0, 3, 0);
} else {
 x_136 = x_120;
}
lean_ctor_set(x_136, 0, x_118);
lean_ctor_set(x_136, 1, x_119);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Lean_Syntax_setTailInfo(x_105, x_136);
return x_137;
}
}
}
}
}
else
{
lean_dec(x_106);
lean_dec(x_105);
return x_95;
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
