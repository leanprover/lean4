// Lean compiler output
// Module: init.lean.parser.transform
// Imports: init.default init.lean.parser.parser
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
uint8_t lean_name_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setTailInfo___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(lean_object*);
extern lean_object* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
lean_object* l_Lean_Syntax_removeParen___closed__1;
extern lean_object* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
lean_object* l_Lean_Syntax_getTailInfo___main___rarg(lean_object*);
uint8_t l_Lean_Syntax_isNone___rarg(lean_object*);
lean_object* l_Lean_Syntax_getArg___rarg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_truncateTrailing(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_push(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_set_x21(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__4;
lean_object* l_Lean_Syntax_manyToSepBy(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___boxed(lean_object*);
lean_object* l_Array_size(lean_object*, lean_object*);
lean_object* l_Array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__3;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs___rarg(lean_object*);
lean_object* l_Lean_Syntax_removeParen___closed__2;
lean_object* l_Lean_Syntax_removeParen(lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_5);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_4, x_4, x_8, x_9);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_12, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_mk_array(x_16, x_15);
x_18 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_12, x_12, x_16, x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_1, x_2, x_3, x_4, x_5);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Syntax_removeParen___closed__4;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_box(0);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_array_get(x_6, x_3, x_7);
x_9 = l_Lean_Syntax_getNumArgs___rarg(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_8);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Syntax_getArg___rarg(x_8, x_7);
x_13 = l_Lean_Syntax_isNone___rarg(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_8);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg___rarg(x_8, x_14);
lean_dec(x_8);
x_16 = lean_array_get(x_6, x_3, x_10);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
lean_dec(x_15);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Syntax_getTailInfo___main___rarg(x_15);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean_string_dec_eq(x_18, x_21);
lean_dec(x_18);
if (x_22 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_inc(x_1);
return x_1;
}
else
{
if (lean_obj_tag(x_20) == 0)
{
lean_dec(x_19);
lean_dec(x_15);
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_26 = lean_ctor_get(x_24, 2);
x_27 = lean_ctor_get(x_19, 2);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_string_utf8_extract(x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_32 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_string_utf8_extract(x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_39 = lean_string_append(x_33, x_38);
lean_dec(x_38);
x_40 = lean_string_utf8_byte_size(x_39);
lean_ctor_set(x_27, 2, x_40);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 0, x_39);
lean_ctor_set(x_24, 2, x_27);
x_41 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
x_44 = lean_ctor_get(x_27, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_45 = lean_string_utf8_extract(x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_46 = lean_string_append(x_33, x_45);
lean_dec(x_45);
x_47 = lean_string_utf8_byte_size(x_46);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_14);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_24, 2, x_48);
x_49 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_50 = lean_ctor_get(x_24, 2);
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
x_53 = lean_ctor_get(x_19, 2);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 2);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_string_utf8_extract(x_54, x_55, x_56);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_58 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_53, 2);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 lean_ctor_release(x_53, 2);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
x_64 = lean_string_utf8_extract(x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_65 = lean_string_append(x_59, x_64);
lean_dec(x_64);
x_66 = lean_string_utf8_byte_size(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 3, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_14);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_51);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_67);
lean_ctor_set(x_20, 0, x_68);
x_69 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_70 = lean_ctor_get(x_20, 0);
lean_inc(x_70);
lean_dec(x_20);
x_71 = lean_ctor_get(x_70, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 x_74 = x_70;
} else {
 lean_dec_ref(x_70);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_19, 2);
lean_inc(x_75);
lean_dec(x_19);
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 2);
lean_inc(x_78);
lean_dec(x_71);
x_79 = lean_string_utf8_extract(x_76, x_77, x_78);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
x_80 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__9___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_ctor_get(x_75, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_75, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_75, 2);
lean_inc(x_84);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 x_85 = x_75;
} else {
 lean_dec_ref(x_75);
 x_85 = lean_box(0);
}
x_86 = lean_string_utf8_extract(x_82, x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
x_87 = lean_string_append(x_81, x_86);
lean_dec(x_86);
x_88 = lean_string_utf8_byte_size(x_87);
if (lean_is_scalar(x_85)) {
 x_89 = lean_alloc_ctor(0, 3, 0);
} else {
 x_89 = x_85;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_14);
lean_ctor_set(x_89, 2, x_88);
if (lean_is_scalar(x_74)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_74;
}
lean_ctor_set(x_90, 0, x_72);
lean_ctor_set(x_90, 1, x_73);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_91);
return x_92;
}
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_inc(x_1);
return x_1;
}
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
lean_object* initialize_init_default(lean_object*);
lean_object* initialize_init_lean_parser_parser(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_init_lean_parser_transform(lean_object* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean_io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (lean_io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (lean_io_result_is_error(w)) return w;
l_Lean_Syntax_removeParen___closed__1 = _init_l_Lean_Syntax_removeParen___closed__1();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__1);
l_Lean_Syntax_removeParen___closed__2 = _init_l_Lean_Syntax_removeParen___closed__2();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__2);
l_Lean_Syntax_removeParen___closed__3 = _init_l_Lean_Syntax_removeParen___closed__3();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__3);
l_Lean_Syntax_removeParen___closed__4 = _init_l_Lean_Syntax_removeParen___closed__4();
lean_mark_persistent(l_Lean_Syntax_removeParen___closed__4);
return w;
}
#ifdef __cplusplus
}
#endif
