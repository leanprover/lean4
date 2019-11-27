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
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Syntax_getArg___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo___main___rarg(lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___boxed(lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_truncateTrailing(lean_object*);
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
lean_object* l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
lean_object* l_Lean_Syntax_getNumArgs___rarg(lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
uint8_t l_Lean_Syntax_isNone___rarg(lean_object*);
lean_object* l_Lean_Syntax_removeParen(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__3;
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
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
x_9 = l_Array_back___at___private_Init_Lean_Parser_Parser_6__updateCache___spec__1(x_5);
x_10 = l_Lean_Syntax_getTailInfo___main___rarg(x_9);
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
x_20 = l_Lean_Syntax_setTailInfo___rarg(x_9, x_10);
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
x_32 = l_Lean_Syntax_setTailInfo___rarg(x_9, x_31);
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
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = l_Lean_mkOptionalNode___rarg___closed__1;
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
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_13, x_15);
x_17 = l_Lean_mkOptionalNode___rarg___closed__1;
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
lean_object* _init_l_Lean_Syntax_removeParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_removeParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Syntax_removeParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Syntax_removeParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
lean_object* _init_l_Lean_Syntax_removeParen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_removeParen___closed__2;
x_2 = l_Lean_Syntax_removeParen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Syntax_removeParen(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_removeParen___closed__4;
x_5 = lean_name_eq(x_2, x_4);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_8 = lean_box(0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_array_get(x_8, x_3, x_9);
x_97 = l_Lean_Syntax_getNumArgs___rarg(x_10);
x_98 = lean_unsigned_to_nat(2u);
x_99 = lean_nat_dec_eq(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
x_11 = x_6;
goto block_96;
}
else
{
uint8_t x_100; 
x_100 = 0;
x_11 = x_100;
goto block_96;
}
block_96:
{
uint8_t x_12; 
x_12 = l_Bool_DecidableEq(x_11, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = l_Lean_Syntax_getArg___rarg(x_10, x_9);
x_14 = l_Lean_Syntax_isNone___rarg(x_13);
lean_dec(x_13);
x_15 = l_Bool_DecidableEq(x_14, x_6);
if (x_15 == 0)
{
lean_dec(x_10);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg___rarg(x_10, x_16);
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_array_get(x_8, x_3, x_18);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Syntax_getTailInfo___main___rarg(x_17);
x_24 = l_Option_HasRepr___rarg___closed__3;
x_25 = lean_string_dec_eq(x_21, x_24);
lean_dec(x_21);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_inc(x_1);
return x_1;
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_27, 2);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_string_utf8_extract(x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_35 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_36 = lean_string_append(x_34, x_35);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
x_40 = lean_ctor_get(x_30, 2);
x_41 = lean_string_utf8_extract(x_38, x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
x_42 = lean_string_append(x_36, x_41);
lean_dec(x_41);
x_43 = lean_string_utf8_byte_size(x_42);
lean_ctor_set(x_30, 2, x_43);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 0, x_42);
lean_ctor_set(x_27, 2, x_30);
x_44 = l_Lean_Syntax_setTailInfo___rarg(x_17, x_23);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_30, 0);
x_46 = lean_ctor_get(x_30, 1);
x_47 = lean_ctor_get(x_30, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_30);
x_48 = lean_string_utf8_extract(x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_49 = lean_string_append(x_36, x_48);
lean_dec(x_48);
x_50 = lean_string_utf8_byte_size(x_49);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_16);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_27, 2, x_51);
x_52 = l_Lean_Syntax_setTailInfo___rarg(x_17, x_23);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_27, 2);
x_54 = lean_ctor_get(x_27, 0);
x_55 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_27);
x_56 = lean_ctor_get(x_22, 2);
lean_inc(x_56);
lean_dec(x_22);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 2);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_string_utf8_extract(x_57, x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
x_61 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_ctor_get(x_56, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 2);
lean_inc(x_65);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 x_66 = x_56;
} else {
 lean_dec_ref(x_56);
 x_66 = lean_box(0);
}
x_67 = lean_string_utf8_extract(x_63, x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
x_68 = lean_string_append(x_62, x_67);
lean_dec(x_67);
x_69 = lean_string_utf8_byte_size(x_68);
if (lean_is_scalar(x_66)) {
 x_70 = lean_alloc_ctor(0, 3, 0);
} else {
 x_70 = x_66;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_16);
lean_ctor_set(x_70, 2, x_69);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_54);
lean_ctor_set(x_71, 1, x_55);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_23, 0, x_71);
x_72 = l_Lean_Syntax_setTailInfo___rarg(x_17, x_23);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_73 = lean_ctor_get(x_23, 0);
lean_inc(x_73);
lean_dec(x_23);
x_74 = lean_ctor_get(x_73, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_22, 2);
lean_inc(x_78);
lean_dec(x_22);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 2);
lean_inc(x_81);
lean_dec(x_74);
x_82 = lean_string_utf8_extract(x_79, x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
x_83 = l_Array_forMAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_84 = lean_string_append(x_82, x_83);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_78, 2);
lean_inc(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 lean_ctor_release(x_78, 2);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
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
lean_ctor_set(x_92, 1, x_16);
lean_ctor_set(x_92, 2, x_91);
if (lean_is_scalar(x_77)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_77;
}
lean_ctor_set(x_93, 0, x_75);
lean_ctor_set(x_93, 1, x_76);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = l_Lean_Syntax_setTailInfo___rarg(x_17, x_94);
return x_95;
}
}
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_17);
lean_inc(x_1);
return x_1;
}
}
}
else
{
lean_dec(x_10);
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
l_Lean_Syntax_removeParen___closed__1 = _init_l_Lean_Syntax_removeParen___closed__1();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__1);
l_Lean_Syntax_removeParen___closed__2 = _init_l_Lean_Syntax_removeParen___closed__2();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__2);
l_Lean_Syntax_removeParen___closed__3 = _init_l_Lean_Syntax_removeParen___closed__3();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__3);
l_Lean_Syntax_removeParen___closed__4 = _init_l_Lean_Syntax_removeParen___closed__4();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__4);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
