// Lean compiler output
// Module: init.lean.parser.transform
// Imports: init.default init.lean.parser.parser
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Syntax_setTailInfo___rarg(obj*, obj*);
extern "C" obj* lean_nat_sub(obj*, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(obj*);
extern obj* l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
obj* l_Lean_Syntax_removeParen___closed__1;
obj* l_Lean_Syntax_getTailInfo___main___rarg(obj*);
uint8 l_Lean_Syntax_isNone___rarg(obj*);
obj* l_Lean_Syntax_getArg___rarg(obj*, obj*);
extern "C" obj* lean_string_append(obj*, obj*);
extern obj* l_Option_HasRepr___rarg___closed__3;
extern "C" uint8 lean_nat_dec_lt(obj*, obj*);
obj* l_Lean_SourceInfo_truncateTrailing(obj*);
obj* l_Array_fget(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
extern "C" obj* lean_nat_add(obj*, obj*);
extern "C" uint8 lean_nat_dec_eq(obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
extern "C" uint8 lean_string_dec_eq(obj*, obj*);
obj* l_Lean_Syntax_removeParen___closed__4;
obj* l_Lean_Syntax_manyToSepBy(obj*, obj*);
obj* l_Lean_Syntax_removeParen___boxed(obj*);
obj* l_Array_size(obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
extern obj* l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
extern "C" obj* lean_string_utf8_extract(obj*, obj*, obj*);
obj* l_Lean_Syntax_removeParen___closed__3;
extern "C" obj* lean_string_utf8_byte_size(obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_Lean_Syntax_getNumArgs___rarg(obj*);
obj* l_Lean_Syntax_removeParen___closed__2;
obj* l_Lean_Syntax_removeParen(obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Array_back___at___private_init_lean_parser_parser_6__updateCache___spec__1(x_5);
x_10 = l_Lean_Syntax_getTailInfo___main___rarg(x_9);
x_11 = lean::mk_nat_obj(1u);
x_12 = lean_nat_add(x_4, x_11);
lean::dec(x_4);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_9);
lean::inc(x_1);
x_13 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_1);
x_14 = lean_array_push(x_5, x_13);
x_15 = lean_array_push(x_14, x_8);
x_4 = x_12;
x_5 = x_15;
goto _start;
}
else
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_10);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
x_19 = l_Lean_SourceInfo_truncateTrailing(x_18);
lean::cnstr_set(x_10, 0, x_19);
x_20 = l_Lean_Syntax_setTailInfo___rarg(x_9, x_10);
x_21 = lean_array_get_size(x_5);
x_22 = lean_nat_sub(x_21, x_11);
lean::dec(x_21);
x_23 = lean_array_set(x_5, x_22, x_20);
lean::dec(x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_18);
lean::inc(x_1);
x_25 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_1);
x_26 = lean_array_push(x_23, x_25);
x_27 = lean_array_push(x_26, x_8);
x_4 = x_12;
x_5 = x_27;
goto _start;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_29 = lean::cnstr_get(x_10, 0);
lean::inc(x_29);
lean::dec(x_10);
lean::inc(x_29);
x_30 = l_Lean_SourceInfo_truncateTrailing(x_29);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = l_Lean_Syntax_setTailInfo___rarg(x_9, x_31);
x_33 = lean_array_get_size(x_5);
x_34 = lean_nat_sub(x_33, x_11);
lean::dec(x_33);
x_35 = lean_array_set(x_5, x_34, x_32);
lean::dec(x_34);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_29);
lean::inc(x_1);
x_37 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_1);
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
obj* l_Lean_Syntax_manyToSepBy(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 1);
x_5 = lean::box(0);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_4, x_4, x_8, x_9);
lean::dec(x_4);
lean::cnstr_set(x_1, 1, x_10);
return x_1;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_1);
x_13 = lean::box(0);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean_array_get(x_13, x_12, x_14);
x_16 = lean::mk_nat_obj(1u);
x_17 = lean_mk_array(x_16, x_15);
x_18 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_2, x_12, x_12, x_16, x_17);
lean::dec(x_12);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean::dec(x_2);
return x_1;
}
}
}
obj* l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_Lean_Syntax_manyToSepBy___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* _init_l_Lean_Syntax_removeParen___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("Term");
return x_1;
}
}
obj* _init_l_Lean_Syntax_removeParen___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_declareLeadingBuiltinParser___closed__1;
x_2 = l_Lean_Syntax_removeParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Syntax_removeParen___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("paren");
return x_1;
}
}
obj* _init_l_Lean_Syntax_removeParen___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Syntax_removeParen___closed__2;
x_2 = l_Lean_Syntax_removeParen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Syntax_removeParen(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; obj* x_3; obj* x_4; uint8 x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = l_Lean_Syntax_removeParen___closed__4;
x_5 = lean_name_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean::inc(x_1);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = lean::box(0);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean_array_get(x_6, x_3, x_7);
x_9 = l_Lean_Syntax_getNumArgs___rarg(x_8);
x_10 = lean::mk_nat_obj(2u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean::dec(x_9);
if (x_11 == 0)
{
lean::dec(x_8);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_12; uint8 x_13; 
x_12 = l_Lean_Syntax_getArg___rarg(x_8, x_7);
x_13 = l_Lean_Syntax_isNone___rarg(x_12);
lean::dec(x_12);
if (x_13 == 0)
{
lean::dec(x_8);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::mk_nat_obj(0u);
x_15 = l_Lean_Syntax_getArg___rarg(x_8, x_14);
lean::dec(x_8);
x_16 = lean_array_get(x_6, x_3, x_10);
if (lean::obj_tag(x_16) == 2)
{
obj* x_17; 
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
lean::dec(x_16);
lean::dec(x_15);
lean::inc(x_1);
return x_1;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_18 = lean::cnstr_get(x_16, 1);
lean::inc(x_18);
lean::dec(x_16);
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_20 = l_Lean_Syntax_getTailInfo___main___rarg(x_15);
x_21 = l_Option_HasRepr___rarg___closed__3;
x_22 = lean_string_dec_eq(x_18, x_21);
lean::dec(x_18);
if (x_22 == 0)
{
lean::dec(x_20);
lean::dec(x_19);
lean::dec(x_15);
lean::inc(x_1);
return x_1;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
lean::dec(x_19);
lean::dec(x_15);
lean::inc(x_1);
return x_1;
}
else
{
uint8 x_23; 
x_23 = !lean::is_exclusive(x_20);
if (x_23 == 0)
{
obj* x_24; uint8 x_25; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; uint8 x_34; 
x_26 = lean::cnstr_get(x_24, 2);
x_27 = lean::cnstr_get(x_19, 2);
lean::inc(x_27);
lean::dec(x_19);
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_26, 2);
lean::inc(x_30);
lean::dec(x_26);
x_31 = lean_string_utf8_extract(x_28, x_29, x_30);
lean::dec(x_30);
lean::dec(x_29);
lean::dec(x_28);
x_32 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = !lean::is_exclusive(x_27);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_27, 0);
x_36 = lean::cnstr_get(x_27, 1);
x_37 = lean::cnstr_get(x_27, 2);
x_38 = lean_string_utf8_extract(x_35, x_36, x_37);
lean::dec(x_37);
lean::dec(x_36);
lean::dec(x_35);
x_39 = lean_string_append(x_33, x_38);
lean::dec(x_38);
x_40 = lean_string_utf8_byte_size(x_39);
lean::cnstr_set(x_27, 2, x_40);
lean::cnstr_set(x_27, 1, x_14);
lean::cnstr_set(x_27, 0, x_39);
lean::cnstr_set(x_24, 2, x_27);
x_41 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_41;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_27, 0);
x_43 = lean::cnstr_get(x_27, 1);
x_44 = lean::cnstr_get(x_27, 2);
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_27);
x_45 = lean_string_utf8_extract(x_42, x_43, x_44);
lean::dec(x_44);
lean::dec(x_43);
lean::dec(x_42);
x_46 = lean_string_append(x_33, x_45);
lean::dec(x_45);
x_47 = lean_string_utf8_byte_size(x_46);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_14);
lean::cnstr_set(x_48, 2, x_47);
lean::cnstr_set(x_24, 2, x_48);
x_49 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_49;
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_50 = lean::cnstr_get(x_24, 2);
x_51 = lean::cnstr_get(x_24, 0);
x_52 = lean::cnstr_get(x_24, 1);
lean::inc(x_50);
lean::inc(x_52);
lean::inc(x_51);
lean::dec(x_24);
x_53 = lean::cnstr_get(x_19, 2);
lean::inc(x_53);
lean::dec(x_19);
x_54 = lean::cnstr_get(x_50, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_50, 1);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_50, 2);
lean::inc(x_56);
lean::dec(x_50);
x_57 = lean_string_utf8_extract(x_54, x_55, x_56);
lean::dec(x_56);
lean::dec(x_55);
lean::dec(x_54);
x_58 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean::cnstr_get(x_53, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_53, 1);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_53, 2);
lean::inc(x_62);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 lean::cnstr_release(x_53, 1);
 lean::cnstr_release(x_53, 2);
 x_63 = x_53;
} else {
 lean::dec_ref(x_53);
 x_63 = lean::box(0);
}
x_64 = lean_string_utf8_extract(x_60, x_61, x_62);
lean::dec(x_62);
lean::dec(x_61);
lean::dec(x_60);
x_65 = lean_string_append(x_59, x_64);
lean::dec(x_64);
x_66 = lean_string_utf8_byte_size(x_65);
if (lean::is_scalar(x_63)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_63;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_14);
lean::cnstr_set(x_67, 2, x_66);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_51);
lean::cnstr_set(x_68, 1, x_52);
lean::cnstr_set(x_68, 2, x_67);
lean::cnstr_set(x_20, 0, x_68);
x_69 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_20);
return x_69;
}
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_70 = lean::cnstr_get(x_20, 0);
lean::inc(x_70);
lean::dec(x_20);
x_71 = lean::cnstr_get(x_70, 2);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 lean::cnstr_release(x_70, 2);
 x_74 = x_70;
} else {
 lean::dec_ref(x_70);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_19, 2);
lean::inc(x_75);
lean::dec(x_19);
x_76 = lean::cnstr_get(x_71, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_71, 1);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_71, 2);
lean::inc(x_78);
lean::dec(x_71);
x_79 = lean_string_utf8_extract(x_76, x_77, x_78);
lean::dec(x_78);
lean::dec(x_77);
lean::dec(x_76);
x_80 = l_Array_mforAux___main___at_Lean_Environment_displayStats___spec__10___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean::cnstr_get(x_75, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_75, 1);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_75, 2);
lean::inc(x_84);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 lean::cnstr_release(x_75, 2);
 x_85 = x_75;
} else {
 lean::dec_ref(x_75);
 x_85 = lean::box(0);
}
x_86 = lean_string_utf8_extract(x_82, x_83, x_84);
lean::dec(x_84);
lean::dec(x_83);
lean::dec(x_82);
x_87 = lean_string_append(x_81, x_86);
lean::dec(x_86);
x_88 = lean_string_utf8_byte_size(x_87);
if (lean::is_scalar(x_85)) {
 x_89 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_89 = x_85;
}
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_14);
lean::cnstr_set(x_89, 2, x_88);
if (lean::is_scalar(x_74)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_74;
}
lean::cnstr_set(x_90, 0, x_72);
lean::cnstr_set(x_90, 1, x_73);
lean::cnstr_set(x_90, 2, x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_92 = l_Lean_Syntax_setTailInfo___rarg(x_15, x_91);
return x_92;
}
}
}
}
}
else
{
lean::dec(x_16);
lean::dec(x_15);
lean::inc(x_1);
return x_1;
}
}
}
}
}
else
{
lean::inc(x_1);
return x_1;
}
}
}
obj* l_Lean_Syntax_removeParen___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Syntax_removeParen(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* initialize_init_default(obj*);
obj* initialize_init_lean_parser_parser(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_transform(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (lean::io_result_is_error(w)) return w;
w = initialize_init_default(w);
if (lean::io_result_is_error(w)) return w;
w = initialize_init_lean_parser_parser(w);
if (lean::io_result_is_error(w)) return w;
l_Lean_Syntax_removeParen___closed__1 = _init_l_Lean_Syntax_removeParen___closed__1();
lean::mark_persistent(l_Lean_Syntax_removeParen___closed__1);
l_Lean_Syntax_removeParen___closed__2 = _init_l_Lean_Syntax_removeParen___closed__2();
lean::mark_persistent(l_Lean_Syntax_removeParen___closed__2);
l_Lean_Syntax_removeParen___closed__3 = _init_l_Lean_Syntax_removeParen___closed__3();
lean::mark_persistent(l_Lean_Syntax_removeParen___closed__3);
l_Lean_Syntax_removeParen___closed__4 = _init_l_Lean_Syntax_removeParen___closed__4();
lean::mark_persistent(l_Lean_Syntax_removeParen___closed__4);
return w;
}
