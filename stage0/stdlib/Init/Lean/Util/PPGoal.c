// Lean compiler output
// Module: Init.Lean.Util.PPGoal
// Imports: Init.Lean.Util.PPExt
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__2;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Format_isNil(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_group(lean_object*);
lean_object* lean_metavar_ctx_find_decl(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__5;
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__3;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__8;
lean_object* l_Lean_ppGoal___closed__7;
lean_object* l_Lean_ppGoal___closed__1;
lean_object* l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_5);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
lean_inc(x_2);
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_4, x_2);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_13);
return x_16;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_6, x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_11, x_8);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_7, x_13);
lean_dec(x_7);
x_7 = x_14;
x_8 = x_12;
goto _start;
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" : ");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" :=");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_17 = x_11;
} else {
 lean_dec_ref(x_11);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_21 = x_15;
} else {
 lean_dec_ref(x_15);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 3);
lean_inc(x_23);
lean_dec(x_16);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_87; 
x_87 = 1;
x_27 = x_87;
goto block_86;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_19, 0);
lean_inc(x_88);
x_89 = lean_expr_eqv(x_88, x_25);
lean_dec(x_88);
x_27 = x_89;
goto block_86;
}
block_86:
{
uint8_t x_28; 
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Format_isNil(x_20);
x_30 = l_coeDecidableEq(x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_25);
if (x_30 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_19);
if (lean_is_scalar(x_26)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_26;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_21)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_21;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_7 = x_13;
x_8 = x_38;
goto _start;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_18);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_36);
if (lean_is_scalar(x_21)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_21;
}
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_40);
x_7 = x_13;
x_8 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
lean_dec(x_19);
x_44 = l_Lean_Format_flatten___main___closed__1;
x_45 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_44);
x_46 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_34);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_43);
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_34);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_34);
x_53 = lean_format_group(x_52);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_34);
if (lean_is_scalar(x_26)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_26;
}
lean_ctor_set(x_55, 0, x_33);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_21)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_21;
}
lean_ctor_set(x_56, 0, x_32);
lean_ctor_set(x_56, 1, x_55);
x_7 = x_13;
x_8 = x_56;
goto _start;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_19);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_21;
}
lean_ctor_set(x_59, 0, x_32);
lean_ctor_set(x_59, 1, x_58);
x_7 = x_13;
x_8 = x_59;
goto _start;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
if (lean_is_scalar(x_26)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_26;
}
lean_ctor_set(x_61, 0, x_33);
lean_ctor_set(x_61, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_21;
}
lean_ctor_set(x_62, 0, x_32);
lean_ctor_set(x_62, 1, x_61);
x_7 = x_13;
x_8 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
lean_dec(x_19);
x_65 = l_Lean_Format_flatten___main___closed__1;
x_66 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_65);
x_67 = 0;
x_68 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_67);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_64);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_67);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_67);
x_76 = lean_format_group(x_75);
x_77 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_77, 0, x_20);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_67);
if (lean_is_scalar(x_26)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_26;
}
lean_ctor_set(x_78, 0, x_33);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_21)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_21;
}
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_13;
x_8 = x_79;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_22);
lean_ctor_set(x_81, 1, x_18);
if (lean_is_scalar(x_17)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_17;
}
lean_ctor_set(x_82, 0, x_25);
if (lean_is_scalar(x_26)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_26;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_21;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_7 = x_13;
x_8 = x_84;
goto _start;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_17);
x_90 = lean_ctor_get(x_8, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_15, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_15, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_94 = x_15;
} else {
 lean_dec_ref(x_15);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_16, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_16, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_16, 4);
lean_inc(x_97);
lean_dec(x_16);
x_98 = l_Lean_Format_isNil(x_93);
x_99 = l_coeDecidableEq(x_98);
lean_inc(x_2);
x_100 = l_Lean_MetavarContext_instantiateMVars(x_2, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_2);
x_102 = l_Lean_MetavarContext_instantiateMVars(x_2, x_97);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_95);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = 0;
x_108 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_109 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_110 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_101);
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_107);
x_112 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_103);
x_115 = lean_box(1);
x_116 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_107);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_107);
x_120 = lean_format_group(x_119);
x_121 = lean_box(0);
x_122 = lean_box(0);
if (x_99 == 0)
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_158, 0, x_93);
lean_ctor_set(x_158, 1, x_115);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_107);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_159; uint8_t x_160; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
x_159 = l_Lean_Format_isNil(x_158);
x_160 = l_coeDecidableEq(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_115);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_107);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_120);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_107);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_122);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_121);
lean_ctor_set(x_164, 1, x_163);
x_7 = x_13;
x_8 = x_164;
goto _start;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_120);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_107);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_122);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_121);
lean_ctor_set(x_168, 1, x_167);
x_7 = x_13;
x_8 = x_168;
goto _start;
}
}
else
{
x_123 = x_158;
goto block_157;
}
}
else
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
x_170 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_170, 0, x_93);
lean_ctor_set(x_170, 1, x_120);
lean_ctor_set_uint8(x_170, sizeof(void*)*2, x_107);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_122);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_121);
lean_ctor_set(x_172, 1, x_171);
x_7 = x_13;
x_8 = x_172;
goto _start;
}
else
{
x_123 = x_93;
goto block_157;
}
}
block_157:
{
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_124; uint8_t x_125; 
lean_dec(x_90);
x_124 = l_Lean_Format_isNil(x_123);
x_125 = l_coeDecidableEq(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_107);
x_127 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_94;
}
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_91)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_91;
}
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_128);
x_7 = x_13;
x_8 = x_129;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_94;
}
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_131);
if (lean_is_scalar(x_91)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_91;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_132);
x_7 = x_13;
x_8 = x_133;
goto _start;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; 
x_135 = lean_ctor_get(x_92, 0);
lean_inc(x_135);
lean_dec(x_92);
x_136 = l_Lean_Format_flatten___main___closed__1;
x_137 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_90, x_136);
x_138 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_140 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_135);
x_141 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_141, 0, x_115);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*2, x_107);
x_142 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_142, 0, x_117);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_107);
x_144 = lean_format_group(x_143);
x_145 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_107);
x_146 = l_Lean_Format_isNil(x_145);
x_147 = l_coeDecidableEq(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_107);
x_149 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_120);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_94;
}
lean_ctor_set(x_150, 0, x_122);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_91)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_91;
}
lean_ctor_set(x_151, 0, x_121);
lean_ctor_set(x_151, 1, x_150);
x_7 = x_13;
x_8 = x_151;
goto _start;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_120);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_94;
}
lean_ctor_set(x_154, 0, x_122);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_91)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_91;
}
lean_ctor_set(x_155, 0, x_121);
lean_ctor_set(x_155, 1, x_154);
x_7 = x_13;
x_8 = x_155;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(x_1, x_2, x_3, x_4, x_7, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(x_1, x_2, x_3, x_4, x_10, x_10, x_11, x_6);
return x_12;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_fget(x_6, x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 0)
{
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_17 = x_11;
} else {
 lean_dec_ref(x_11);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_21 = x_15;
} else {
 lean_dec_ref(x_15);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 3);
lean_inc(x_23);
lean_dec(x_16);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_26 = x_24;
} else {
 lean_dec_ref(x_24);
 x_26 = lean_box(0);
}
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_87; 
x_87 = 1;
x_27 = x_87;
goto block_86;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_19, 0);
lean_inc(x_88);
x_89 = lean_expr_eqv(x_88, x_25);
lean_dec(x_88);
x_27 = x_89;
goto block_86;
}
block_86:
{
uint8_t x_28; 
x_28 = l_coeDecidableEq(x_27);
if (x_28 == 0)
{
uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_Format_isNil(x_20);
x_30 = l_coeDecidableEq(x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_17;
}
lean_ctor_set(x_33, 0, x_25);
if (x_30 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_34);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_19);
if (lean_is_scalar(x_26)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_26;
}
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
if (lean_is_scalar(x_21)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_21;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_7 = x_13;
x_8 = x_38;
goto _start;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_18);
if (lean_is_scalar(x_26)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_26;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_36);
if (lean_is_scalar(x_21)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_21;
}
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_40);
x_7 = x_13;
x_8 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
lean_dec(x_19);
x_44 = l_Lean_Format_flatten___main___closed__1;
x_45 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_44);
x_46 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_34);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_43);
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_34);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_34);
x_53 = lean_format_group(x_52);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_36);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_34);
if (lean_is_scalar(x_26)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_26;
}
lean_ctor_set(x_55, 0, x_33);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_21)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_21;
}
lean_ctor_set(x_56, 0, x_32);
lean_ctor_set(x_56, 1, x_55);
x_7 = x_13;
x_8 = x_56;
goto _start;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_19);
if (lean_is_scalar(x_26)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_26;
}
lean_ctor_set(x_58, 0, x_33);
lean_ctor_set(x_58, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_21;
}
lean_ctor_set(x_59, 0, x_32);
lean_ctor_set(x_59, 1, x_58);
x_7 = x_13;
x_8 = x_59;
goto _start;
}
else
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_18);
if (lean_is_scalar(x_26)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_26;
}
lean_ctor_set(x_61, 0, x_33);
lean_ctor_set(x_61, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_21;
}
lean_ctor_set(x_62, 0, x_32);
lean_ctor_set(x_62, 1, x_61);
x_7 = x_13;
x_8 = x_62;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_64 = lean_ctor_get(x_19, 0);
lean_inc(x_64);
lean_dec(x_19);
x_65 = l_Lean_Format_flatten___main___closed__1;
x_66 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_65);
x_67 = 0;
x_68 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_67);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_64);
x_71 = lean_box(1);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_67);
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_67);
x_76 = lean_format_group(x_75);
x_77 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_77, 0, x_20);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*2, x_67);
if (lean_is_scalar(x_26)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_26;
}
lean_ctor_set(x_78, 0, x_33);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_21)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_21;
}
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_78);
x_7 = x_13;
x_8 = x_79;
goto _start;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_22);
lean_ctor_set(x_81, 1, x_18);
if (lean_is_scalar(x_17)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_17;
}
lean_ctor_set(x_82, 0, x_25);
if (lean_is_scalar(x_26)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_26;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_20);
if (lean_is_scalar(x_21)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_21;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_7 = x_13;
x_8 = x_84;
goto _start;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_17);
x_90 = lean_ctor_get(x_8, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_15, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_15, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_94 = x_15;
} else {
 lean_dec_ref(x_15);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_16, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_16, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_16, 4);
lean_inc(x_97);
lean_dec(x_16);
x_98 = l_Lean_Format_isNil(x_93);
x_99 = l_coeDecidableEq(x_98);
lean_inc(x_2);
x_100 = l_Lean_MetavarContext_instantiateMVars(x_2, x_96);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_2);
x_102 = l_Lean_MetavarContext_instantiateMVars(x_2, x_97);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_95);
x_106 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = 0;
x_108 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_109 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_110 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_101);
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_107);
x_112 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_103);
x_115 = lean_box(1);
x_116 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_107);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_119, 0, x_113);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set_uint8(x_119, sizeof(void*)*2, x_107);
x_120 = lean_format_group(x_119);
x_121 = lean_box(0);
x_122 = lean_box(0);
if (x_99 == 0)
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_158, 0, x_93);
lean_ctor_set(x_158, 1, x_115);
lean_ctor_set_uint8(x_158, sizeof(void*)*2, x_107);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_159; uint8_t x_160; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
x_159 = l_Lean_Format_isNil(x_158);
x_160 = l_coeDecidableEq(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_115);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_107);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_120);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_107);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_122);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_121);
lean_ctor_set(x_164, 1, x_163);
x_7 = x_13;
x_8 = x_164;
goto _start;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_120);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_107);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_122);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_121);
lean_ctor_set(x_168, 1, x_167);
x_7 = x_13;
x_8 = x_168;
goto _start;
}
}
else
{
x_123 = x_158;
goto block_157;
}
}
else
{
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
x_170 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_170, 0, x_93);
lean_ctor_set(x_170, 1, x_120);
lean_ctor_set_uint8(x_170, sizeof(void*)*2, x_107);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_122);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_121);
lean_ctor_set(x_172, 1, x_171);
x_7 = x_13;
x_8 = x_172;
goto _start;
}
else
{
x_123 = x_93;
goto block_157;
}
}
block_157:
{
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_124; uint8_t x_125; 
lean_dec(x_90);
x_124 = l_Lean_Format_isNil(x_123);
x_125 = l_coeDecidableEq(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_115);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_107);
x_127 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_94;
}
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_91)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_91;
}
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_128);
x_7 = x_13;
x_8 = x_129;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_120);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_94;
}
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_131);
if (lean_is_scalar(x_91)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_91;
}
lean_ctor_set(x_133, 0, x_121);
lean_ctor_set(x_133, 1, x_132);
x_7 = x_13;
x_8 = x_133;
goto _start;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint8_t x_147; 
x_135 = lean_ctor_get(x_92, 0);
lean_inc(x_135);
lean_dec(x_92);
x_136 = l_Lean_Format_flatten___main___closed__1;
x_137 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_90, x_136);
x_138 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_107);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_140 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_135);
x_141 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_141, 0, x_115);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*2, x_107);
x_142 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_142, 0, x_117);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*2, x_107);
x_144 = lean_format_group(x_143);
x_145 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_107);
x_146 = l_Lean_Format_isNil(x_145);
x_147 = l_coeDecidableEq(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_115);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_107);
x_149 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_120);
lean_ctor_set_uint8(x_149, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_94;
}
lean_ctor_set(x_150, 0, x_122);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_91)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_91;
}
lean_ctor_set(x_151, 0, x_121);
lean_ctor_set(x_151, 1, x_150);
x_7 = x_13;
x_8 = x_151;
goto _start;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_153, 0, x_145);
lean_ctor_set(x_153, 1, x_120);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_107);
if (lean_is_scalar(x_94)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_94;
}
lean_ctor_set(x_154, 0, x_122);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_91)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_91;
}
lean_ctor_set(x_155, 0, x_121);
lean_ctor_set(x_155, 1, x_154);
x_7 = x_13;
x_8 = x_155;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_7, x_6);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_ppGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown goal");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ppGoal___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ppGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ppGoal___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ppGoal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("⊢");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_ppGoal___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("case ");
return x_1;
}
}
lean_object* _init_l_Lean_ppGoal___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppGoal___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_2);
x_6 = lean_metavar_ctx_find_decl(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = l_Lean_ppGoal___closed__2;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = l_Lean_ppGoal___closed__4;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(x_1, x_2, x_3, x_4, x_9, x_10);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Format_isNil(x_15);
x_17 = l_coeDecidableEq(x_16);
x_18 = lean_ctor_get(x_8, 2);
lean_inc(x_18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_18);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_ctor_get(x_8, 0);
lean_inc(x_22);
lean_dec(x_8);
if (x_17 == 0)
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_62 = 0;
x_63 = lean_box(1);
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_64;
goto block_61;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_64;
goto block_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_14, 0);
lean_inc(x_65);
lean_dec(x_14);
x_66 = l_Lean_Format_flatten___main___closed__1;
x_67 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_13, x_66);
x_68 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_62);
x_70 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_65);
x_71 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_62);
x_72 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_72, 0, x_20);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_62);
x_74 = lean_format_group(x_73);
x_75 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*2, x_62);
x_23 = x_75;
goto block_61;
}
}
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_15;
goto block_61;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = x_15;
goto block_61;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_14, 0);
lean_inc(x_76);
lean_dec(x_14);
x_77 = l_Lean_Format_flatten___main___closed__1;
x_78 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_13, x_77);
x_79 = 0;
x_80 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_81 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*2, x_79);
x_82 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_76);
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_79);
x_85 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_79);
x_87 = lean_format_group(x_86);
x_88 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_88, 0, x_15);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*2, x_79);
x_23 = x_88;
goto block_61;
}
}
}
block_61:
{
uint8_t x_24; uint8_t x_25; 
x_24 = l_Lean_Format_isNil(x_23);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = 0;
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
x_29 = l_Lean_ppGoal___closed__6;
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_26);
x_31 = l_Lean_Format_flatten___main___closed__1;
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_26);
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_26);
if (lean_obj_tag(x_22) == 0)
{
return x_33;
}
else
{
lean_object* x_43; 
x_43 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_34);
x_35 = l_Lean_Name_toString___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_22);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_ppGoal___closed__8;
x_39 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_26);
x_40 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_26);
x_41 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set_uint8(x_41, sizeof(void*)*2, x_26);
return x_41;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = 0;
x_45 = l_Lean_ppGoal___closed__6;
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_23);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_44);
x_47 = l_Lean_Format_flatten___main___closed__1;
x_48 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_44);
x_49 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_21);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_44);
if (lean_obj_tag(x_22) == 0)
{
return x_49;
}
else
{
lean_object* x_60; 
x_60 = lean_box(0);
x_50 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
x_51 = l_Lean_Name_toString___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_22);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_ppGoal___closed__8;
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_44);
x_56 = lean_box(1);
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_44);
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_44);
return x_58;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_foldlMAux___main___at_Lean_ppGoal___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* initialize_Init_Lean_Util_PPExt(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Util_PPGoal(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_PPExt(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__1);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__5);
l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6 = _init_l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6);
l_Lean_ppGoal___closed__1 = _init_l_Lean_ppGoal___closed__1();
lean_mark_persistent(l_Lean_ppGoal___closed__1);
l_Lean_ppGoal___closed__2 = _init_l_Lean_ppGoal___closed__2();
lean_mark_persistent(l_Lean_ppGoal___closed__2);
l_Lean_ppGoal___closed__3 = _init_l_Lean_ppGoal___closed__3();
lean_mark_persistent(l_Lean_ppGoal___closed__3);
l_Lean_ppGoal___closed__4 = _init_l_Lean_ppGoal___closed__4();
lean_mark_persistent(l_Lean_ppGoal___closed__4);
l_Lean_ppGoal___closed__5 = _init_l_Lean_ppGoal___closed__5();
lean_mark_persistent(l_Lean_ppGoal___closed__5);
l_Lean_ppGoal___closed__6 = _init_l_Lean_ppGoal___closed__6();
lean_mark_persistent(l_Lean_ppGoal___closed__6);
l_Lean_ppGoal___closed__7 = _init_l_Lean_ppGoal___closed__7();
lean_mark_persistent(l_Lean_ppGoal___closed__7);
l_Lean_ppGoal___closed__8 = _init_l_Lean_ppGoal___closed__8();
lean_mark_persistent(l_Lean_ppGoal___closed__8);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
