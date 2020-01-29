// Lean compiler output
// Module: Init.Lean.Parser.Transform
// Imports: Init.Default Init.Lean.Parser.Parser
#include "runtime/lean.h"
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_truncateTrailing(lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_removeParen(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Syntax_getTailInfo___main(lean_object*);
extern lean_object* l___private_Init_Lean_Parser_Parser_13__antiquotNestedExpr___elambda__1___rarg___closed__2;
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
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__nameLitAux___spec__1(x_5);
x_10 = l_Lean_Syntax_getTailInfo___main(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_inc(x_1);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_array_push(x_5, x_13);
x_15 = lean_array_push(x_14, x_8);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = l_Lean_SourceInfo_truncateTrailing(x_18);
lean_ctor_set(x_10, 0, x_19);
x_20 = l_Lean_Syntax_setTailInfo(x_9, x_10);
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_sub(x_21, x_11);
lean_dec(x_21);
x_23 = lean_array_set(x_5, x_22, x_20);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
lean_inc(x_1);
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_1);
x_26 = lean_array_push(x_23, x_25);
x_27 = lean_array_push(x_26, x_8);
x_4 = x_12;
x_5 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
lean_inc(x_29);
x_30 = l_Lean_SourceInfo_truncateTrailing(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Syntax_setTailInfo(x_9, x_31);
x_33 = lean_array_get_size(x_5);
x_34 = lean_nat_sub(x_33, x_11);
lean_dec(x_33);
x_35 = lean_array_set(x_5, x_34, x_32);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_29);
lean_inc(x_1);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
x_38 = lean_array_push(x_35, x_37);
x_39 = lean_array_push(x_38, x_8);
x_4 = x_12;
x_5 = x_39;
goto _start;
}
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l___private_Init_Lean_Parser_Parser_13__antiquotNestedExpr___elambda__1___rarg___closed__2;
x_5 = lean_name_eq(x_2, x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_7 = l_Lean_Syntax_inhabited;
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_array_get(x_7, x_3, x_8);
x_96 = l_Lean_Syntax_getNumArgs(x_9);
x_97 = lean_unsigned_to_nat(2u);
x_98 = lean_nat_dec_eq(x_96, x_97);
lean_dec(x_96);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = 1;
x_10 = x_99;
goto block_95;
}
else
{
uint8_t x_100; 
x_100 = 0;
x_10 = x_100;
goto block_95;
}
block_95:
{
uint8_t x_11; 
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = l_Lean_Syntax_getArg(x_9, x_8);
x_13 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_dec(x_9);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_9, x_15);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_array_get(x_7, x_3, x_17);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_18);
lean_dec(x_16);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Syntax_getTailInfo___main(x_16);
x_23 = l_Option_HasRepr___rarg___closed__3;
x_24 = lean_string_dec_eq(x_20, x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_inc(x_1);
return x_1;
}
else
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec(x_21);
lean_dec(x_16);
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_26, 2);
x_29 = lean_ctor_get(x_21, 2);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_string_utf8_extract(x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_34 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
x_39 = lean_ctor_get(x_29, 2);
x_40 = lean_string_utf8_extract(x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_41 = lean_string_append(x_35, x_40);
lean_dec(x_40);
x_42 = lean_string_utf8_byte_size(x_41);
lean_ctor_set(x_29, 2, x_42);
lean_ctor_set(x_29, 1, x_15);
lean_ctor_set(x_29, 0, x_41);
lean_ctor_set(x_26, 2, x_29);
x_43 = l_Lean_Syntax_setTailInfo(x_16, x_22);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_29, 0);
x_45 = lean_ctor_get(x_29, 1);
x_46 = lean_ctor_get(x_29, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_29);
x_47 = lean_string_utf8_extract(x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_48 = lean_string_append(x_35, x_47);
lean_dec(x_47);
x_49 = lean_string_utf8_byte_size(x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_15);
lean_ctor_set(x_50, 2, x_49);
lean_ctor_set(x_26, 2, x_50);
x_51 = l_Lean_Syntax_setTailInfo(x_16, x_22);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_52 = lean_ctor_get(x_26, 2);
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_52);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_26);
x_55 = lean_ctor_get(x_21, 2);
lean_inc(x_55);
lean_dec(x_21);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 2);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_string_utf8_extract(x_56, x_57, x_58);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_60 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_61 = lean_string_append(x_59, x_60);
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_55, 2);
lean_inc(x_64);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_65 = x_55;
} else {
 lean_dec_ref(x_55);
 x_65 = lean_box(0);
}
x_66 = lean_string_utf8_extract(x_62, x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_67 = lean_string_append(x_61, x_66);
lean_dec(x_66);
x_68 = lean_string_utf8_byte_size(x_67);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_15);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_53);
lean_ctor_set(x_70, 1, x_54);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_22, 0, x_70);
x_71 = l_Lean_Syntax_setTailInfo(x_16, x_22);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_72 = lean_ctor_get(x_22, 0);
lean_inc(x_72);
lean_dec(x_22);
x_73 = lean_ctor_get(x_72, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 lean_ctor_release(x_72, 2);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_21, 2);
lean_inc(x_77);
lean_dec(x_21);
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_73, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_73, 2);
lean_inc(x_80);
lean_dec(x_73);
x_81 = lean_string_utf8_extract(x_78, x_79, x_80);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
x_82 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_ctor_get(x_77, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 2);
lean_inc(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
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
lean_ctor_set(x_91, 1, x_15);
lean_ctor_set(x_91, 2, x_90);
if (lean_is_scalar(x_76)) {
 x_92 = lean_alloc_ctor(0, 3, 0);
} else {
 x_92 = x_76;
}
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_75);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_Syntax_setTailInfo(x_16, x_93);
return x_94;
}
}
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_16);
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_dec(x_9);
lean_inc(x_1);
return x_1;
}
}
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Lean_Syntax_removeParen___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Syntax_removeParen(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Default(lean_object*);
lean_object* initialize_Init_Lean_Parser_Parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Parser_Transform(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Parser_Parser(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
