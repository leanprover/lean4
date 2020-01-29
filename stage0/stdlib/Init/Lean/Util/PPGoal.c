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
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_11, 0, x_26);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_28);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_11, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_15, 1, x_32);
lean_ctor_set(x_15, 0, x_31);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_11);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_expr_eqv(x_38, x_35);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Format_isNil(x_21);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_35);
if (x_40 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_43);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_45);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = l_Lean_Format_flatten___main___closed__1;
x_48 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_47);
x_49 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_43);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_38);
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_43);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_43);
x_56 = lean_format_group(x_55);
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_43);
lean_ctor_set(x_24, 1, x_57);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = l_Lean_Format_flatten___main___closed__1;
x_61 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_60);
x_62 = 0;
x_63 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_38);
x_66 = lean_box(1);
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_62);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_62);
x_71 = lean_format_group(x_70);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_21);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_62);
lean_ctor_set(x_24, 1, x_72);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_38);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_74);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_20, 0);
lean_inc(x_76);
lean_dec(x_20);
x_77 = lean_expr_eqv(x_76, x_35);
if (x_77 == 0)
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = l_Lean_Format_isNil(x_21);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_22);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_35);
if (x_78 == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_84, 0, x_21);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_82);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_76);
lean_ctor_set(x_24, 1, x_84);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = l_Lean_Format_flatten___main___closed__1;
x_87 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_86);
x_88 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_89 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_82);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_76);
x_91 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*2, x_82);
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_82);
x_95 = lean_format_group(x_94);
x_96 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_82);
lean_ctor_set(x_24, 1, x_96);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_76);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_99 = l_Lean_Format_flatten___main___closed__1;
x_100 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_99);
x_101 = 0;
x_102 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_103 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_101);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_104 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_76);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_101);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_101);
x_110 = lean_format_group(x_109);
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_21);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_101);
lean_ctor_set(x_24, 1, x_111);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_76);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_22);
lean_ctor_set(x_113, 1, x_18);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_114);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_113);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_24, 0);
lean_inc(x_116);
lean_dec(x_24);
x_117 = lean_ctor_get(x_20, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_118 = x_20;
} else {
 lean_dec_ref(x_20);
 x_118 = lean_box(0);
}
x_119 = lean_expr_eqv(x_117, x_116);
if (x_119 == 0)
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = l_Lean_Format_isNil(x_21);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_22);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_116);
if (x_120 == 0)
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_124 = 0;
x_125 = lean_box(1);
x_126 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_126, 0, x_21);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_124);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_127; 
lean_dec(x_117);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_15, 1, x_127);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_129 = l_Lean_Format_flatten___main___closed__1;
x_130 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_129);
x_131 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_132 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*2, x_124);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_133 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_117);
x_134 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*2, x_124);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_124);
x_138 = lean_format_group(x_137);
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_124);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_15, 1, x_140);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_142; 
lean_dec(x_117);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_123);
lean_ctor_set(x_142, 1, x_21);
lean_ctor_set(x_15, 1, x_142);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_144 = l_Lean_Format_flatten___main___closed__1;
x_145 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_144);
x_146 = 0;
x_147 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_146);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_149 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_117);
x_150 = lean_box(1);
x_151 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_146);
x_152 = lean_unsigned_to_nat(2u);
x_153 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_146);
x_155 = lean_format_group(x_154);
x_156 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_156, 0, x_21);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_146);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_123);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_15, 1, x_157);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_117);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_22);
lean_ctor_set(x_159, 1, x_18);
if (lean_is_scalar(x_118)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_118;
}
lean_ctor_set(x_160, 0, x_116);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_21);
lean_ctor_set(x_15, 1, x_161);
lean_ctor_set(x_15, 0, x_159);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_15, 0);
x_164 = lean_ctor_get(x_15, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_15);
x_165 = lean_ctor_get(x_17, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_17, 3);
lean_inc(x_166);
lean_dec(x_17);
lean_inc(x_2);
x_167 = l_Lean_MetavarContext_instantiateMVars(x_2, x_166);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_18);
lean_ctor_set(x_11, 0, x_168);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_11);
lean_ctor_set(x_171, 1, x_164);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_7 = x_13;
x_8 = x_172;
goto _start;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_free_object(x_11);
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_175 = x_167;
} else {
 lean_dec_ref(x_167);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_163, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_177 = x_163;
} else {
 lean_dec_ref(x_163);
 x_177 = lean_box(0);
}
x_178 = lean_expr_eqv(x_176, x_174);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = l_Lean_Format_isNil(x_164);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_165);
lean_ctor_set(x_181, 1, x_180);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_174);
if (x_179 == 0)
{
uint8_t x_183; lean_object* x_184; lean_object* x_185; 
x_183 = 0;
x_184 = lean_box(1);
x_185 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_185, 0, x_164);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*2, x_183);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_176);
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_175;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_186);
x_7 = x_13;
x_8 = x_187;
goto _start;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = l_Lean_Format_flatten___main___closed__1;
x_190 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_189);
x_191 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_192 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*2, x_183);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_193 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_176);
x_194 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_194, 0, x_184);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_183);
x_195 = lean_unsigned_to_nat(2u);
x_196 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_183);
x_198 = lean_format_group(x_197);
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_183);
if (lean_is_scalar(x_175)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_175;
}
lean_ctor_set(x_200, 0, x_182);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_181);
lean_ctor_set(x_201, 1, x_200);
x_7 = x_13;
x_8 = x_201;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_176);
if (lean_is_scalar(x_175)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_175;
}
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_164);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_181);
lean_ctor_set(x_204, 1, x_203);
x_7 = x_13;
x_8 = x_204;
goto _start;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_206 = l_Lean_Format_flatten___main___closed__1;
x_207 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_206);
x_208 = 0;
x_209 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_210 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_208);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_211 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_176);
x_212 = lean_box(1);
x_213 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*2, x_208);
x_214 = lean_unsigned_to_nat(2u);
x_215 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_208);
x_217 = lean_format_group(x_216);
x_218 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_218, 0, x_164);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*2, x_208);
if (lean_is_scalar(x_175)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_175;
}
lean_ctor_set(x_219, 0, x_182);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_181);
lean_ctor_set(x_220, 1, x_219);
x_7 = x_13;
x_8 = x_220;
goto _start;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_176);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_165);
lean_ctor_set(x_222, 1, x_18);
if (lean_is_scalar(x_177)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_177;
}
lean_ctor_set(x_223, 0, x_174);
if (lean_is_scalar(x_175)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_175;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_164);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_7 = x_13;
x_8 = x_225;
goto _start;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_free_object(x_11);
x_227 = lean_ctor_get(x_8, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_228 = x_8;
} else {
 lean_dec_ref(x_8);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_15, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_15, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_231 = x_15;
} else {
 lean_dec_ref(x_15);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_17, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_17, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_17, 4);
lean_inc(x_234);
lean_dec(x_17);
x_235 = l_Lean_Format_isNil(x_230);
lean_inc(x_2);
x_236 = l_Lean_MetavarContext_instantiateMVars(x_2, x_233);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
lean_inc(x_2);
x_238 = l_Lean_MetavarContext_instantiateMVars(x_2, x_234);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec(x_238);
x_240 = l_Lean_Name_toString___closed__1;
x_241 = l_Lean_Name_toStringWithSep___main(x_240, x_232);
x_242 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = 0;
x_244 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_245 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_246 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_237);
x_247 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set_uint8(x_247, sizeof(void*)*2, x_243);
x_248 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_249 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set_uint8(x_249, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_250 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_239);
x_251 = lean_box(1);
x_252 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*2, x_243);
x_253 = lean_unsigned_to_nat(2u);
x_254 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*2, x_243);
x_256 = lean_format_group(x_255);
x_257 = lean_box(0);
x_258 = lean_box(0);
if (x_235 == 0)
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_292, 0, x_230);
lean_ctor_set(x_292, 1, x_251);
lean_ctor_set_uint8(x_292, sizeof(void*)*2, x_243);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_293; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
x_293 = l_Lean_Format_isNil(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_251);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_243);
x_295 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_256);
lean_ctor_set_uint8(x_295, sizeof(void*)*2, x_243);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_258);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_257);
lean_ctor_set(x_297, 1, x_296);
x_7 = x_13;
x_8 = x_297;
goto _start;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_299, 0, x_292);
lean_ctor_set(x_299, 1, x_256);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_243);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_258);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_257);
lean_ctor_set(x_301, 1, x_300);
x_7 = x_13;
x_8 = x_301;
goto _start;
}
}
else
{
x_259 = x_292;
goto block_291;
}
}
else
{
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_230);
lean_ctor_set(x_303, 1, x_256);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_243);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_258);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_257);
lean_ctor_set(x_305, 1, x_304);
x_7 = x_13;
x_8 = x_305;
goto _start;
}
else
{
x_259 = x_230;
goto block_291;
}
}
block_291:
{
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_260; 
lean_dec(x_227);
x_260 = l_Lean_Format_isNil(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_251);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_243);
x_262 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set_uint8(x_262, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_231;
}
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_228)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_228;
}
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_263);
x_7 = x_13;
x_8 = x_264;
goto _start;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_256);
lean_ctor_set_uint8(x_266, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_231;
}
lean_ctor_set(x_267, 0, x_258);
lean_ctor_set(x_267, 1, x_266);
if (lean_is_scalar(x_228)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_228;
}
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_267);
x_7 = x_13;
x_8 = x_268;
goto _start;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_270 = lean_ctor_get(x_229, 0);
lean_inc(x_270);
lean_dec(x_229);
x_271 = l_Lean_Format_flatten___main___closed__1;
x_272 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_227, x_271);
x_273 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_275 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_270);
x_276 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_276, 0, x_251);
lean_ctor_set(x_276, 1, x_275);
lean_ctor_set_uint8(x_276, sizeof(void*)*2, x_243);
x_277 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_277, 0, x_253);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_278, 0, x_274);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*2, x_243);
x_279 = lean_format_group(x_278);
x_280 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_280, 0, x_259);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set_uint8(x_280, sizeof(void*)*2, x_243);
x_281 = l_Lean_Format_isNil(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_251);
lean_ctor_set_uint8(x_282, sizeof(void*)*2, x_243);
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_256);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_231;
}
lean_ctor_set(x_284, 0, x_258);
lean_ctor_set(x_284, 1, x_283);
if (lean_is_scalar(x_228)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_228;
}
lean_ctor_set(x_285, 0, x_257);
lean_ctor_set(x_285, 1, x_284);
x_7 = x_13;
x_8 = x_285;
goto _start;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_287, 0, x_280);
lean_ctor_set(x_287, 1, x_256);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_231;
}
lean_ctor_set(x_288, 0, x_258);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_228)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_228;
}
lean_ctor_set(x_289, 0, x_257);
lean_ctor_set(x_289, 1, x_288);
x_7 = x_13;
x_8 = x_289;
goto _start;
}
}
}
}
}
else
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_11, 0);
lean_inc(x_307);
lean_dec(x_11);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_8, 0);
lean_inc(x_308);
lean_dec(x_8);
x_309 = lean_ctor_get(x_15, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_15, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_311 = x_15;
} else {
 lean_dec_ref(x_15);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_307, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_307, 3);
lean_inc(x_313);
lean_dec(x_307);
lean_inc(x_2);
x_314 = l_Lean_MetavarContext_instantiateMVars(x_2, x_313);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_312);
lean_ctor_set(x_317, 1, x_308);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_315);
if (lean_is_scalar(x_316)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_316;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_311;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_319);
x_7 = x_13;
x_8 = x_320;
goto _start;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_314, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_323 = x_314;
} else {
 lean_dec_ref(x_314);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_309, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_325 = x_309;
} else {
 lean_dec_ref(x_309);
 x_325 = lean_box(0);
}
x_326 = lean_expr_eqv(x_324, x_322);
if (x_326 == 0)
{
uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = l_Lean_Format_isNil(x_310);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_312);
lean_ctor_set(x_329, 1, x_328);
if (lean_is_scalar(x_325)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_325;
}
lean_ctor_set(x_330, 0, x_322);
if (x_327 == 0)
{
uint8_t x_331; lean_object* x_332; lean_object* x_333; 
x_331 = 0;
x_332 = lean_box(1);
x_333 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_333, 0, x_310);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*2, x_331);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_324);
if (lean_is_scalar(x_323)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_323;
}
lean_ctor_set(x_334, 0, x_330);
lean_ctor_set(x_334, 1, x_333);
if (lean_is_scalar(x_311)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_311;
}
lean_ctor_set(x_335, 0, x_329);
lean_ctor_set(x_335, 1, x_334);
x_7 = x_13;
x_8 = x_335;
goto _start;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_337 = l_Lean_Format_flatten___main___closed__1;
x_338 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_337);
x_339 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_340 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set_uint8(x_340, sizeof(void*)*2, x_331);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_341 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_324);
x_342 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_342, 0, x_332);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set_uint8(x_342, sizeof(void*)*2, x_331);
x_343 = lean_unsigned_to_nat(2u);
x_344 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
x_345 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set_uint8(x_345, sizeof(void*)*2, x_331);
x_346 = lean_format_group(x_345);
x_347 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_347, 0, x_333);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*2, x_331);
if (lean_is_scalar(x_323)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_323;
}
lean_ctor_set(x_348, 0, x_330);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_311)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_311;
}
lean_ctor_set(x_349, 0, x_329);
lean_ctor_set(x_349, 1, x_348);
x_7 = x_13;
x_8 = x_349;
goto _start;
}
}
else
{
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_324);
if (lean_is_scalar(x_323)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_323;
}
lean_ctor_set(x_351, 0, x_330);
lean_ctor_set(x_351, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_311;
}
lean_ctor_set(x_352, 0, x_329);
lean_ctor_set(x_352, 1, x_351);
x_7 = x_13;
x_8 = x_352;
goto _start;
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_354 = l_Lean_Format_flatten___main___closed__1;
x_355 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_354);
x_356 = 0;
x_357 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_358 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_356);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_359 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_324);
x_360 = lean_box(1);
x_361 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*2, x_356);
x_362 = lean_unsigned_to_nat(2u);
x_363 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*2, x_356);
x_365 = lean_format_group(x_364);
x_366 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_366, 0, x_310);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*2, x_356);
if (lean_is_scalar(x_323)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_323;
}
lean_ctor_set(x_367, 0, x_330);
lean_ctor_set(x_367, 1, x_366);
if (lean_is_scalar(x_311)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_311;
}
lean_ctor_set(x_368, 0, x_329);
lean_ctor_set(x_368, 1, x_367);
x_7 = x_13;
x_8 = x_368;
goto _start;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_324);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_312);
lean_ctor_set(x_370, 1, x_308);
if (lean_is_scalar(x_325)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_325;
}
lean_ctor_set(x_371, 0, x_322);
if (lean_is_scalar(x_323)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_323;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_311;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_372);
x_7 = x_13;
x_8 = x_373;
goto _start;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_375 = lean_ctor_get(x_8, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_376 = x_8;
} else {
 lean_dec_ref(x_8);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_15, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_15, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_379 = x_15;
} else {
 lean_dec_ref(x_15);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_307, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_307, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_307, 4);
lean_inc(x_382);
lean_dec(x_307);
x_383 = l_Lean_Format_isNil(x_378);
lean_inc(x_2);
x_384 = l_Lean_MetavarContext_instantiateMVars(x_2, x_381);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec(x_384);
lean_inc(x_2);
x_386 = l_Lean_MetavarContext_instantiateMVars(x_2, x_382);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_Lean_Name_toString___closed__1;
x_389 = l_Lean_Name_toStringWithSep___main(x_388, x_380);
x_390 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_390, 0, x_389);
x_391 = 0;
x_392 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_393 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_394 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_385);
x_395 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*2, x_391);
x_396 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_397 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
lean_ctor_set_uint8(x_397, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_387);
x_399 = lean_box(1);
x_400 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*2, x_391);
x_401 = lean_unsigned_to_nat(2u);
x_402 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_403, 0, x_397);
lean_ctor_set(x_403, 1, x_402);
lean_ctor_set_uint8(x_403, sizeof(void*)*2, x_391);
x_404 = lean_format_group(x_403);
x_405 = lean_box(0);
x_406 = lean_box(0);
if (x_383 == 0)
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_378);
lean_ctor_set(x_440, 1, x_399);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_391);
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_441; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_376);
x_441 = l_Lean_Format_isNil(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_399);
lean_ctor_set_uint8(x_442, sizeof(void*)*2, x_391);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_404);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_391);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_406);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_405);
lean_ctor_set(x_445, 1, x_444);
x_7 = x_13;
x_8 = x_445;
goto _start;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_447, 0, x_440);
lean_ctor_set(x_447, 1, x_404);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_391);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_406);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_405);
lean_ctor_set(x_449, 1, x_448);
x_7 = x_13;
x_8 = x_449;
goto _start;
}
}
else
{
x_407 = x_440;
goto block_439;
}
}
else
{
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_376);
x_451 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_451, 0, x_378);
lean_ctor_set(x_451, 1, x_404);
lean_ctor_set_uint8(x_451, sizeof(void*)*2, x_391);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_406);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_405);
lean_ctor_set(x_453, 1, x_452);
x_7 = x_13;
x_8 = x_453;
goto _start;
}
else
{
x_407 = x_378;
goto block_439;
}
}
block_439:
{
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_408; 
lean_dec(x_375);
x_408 = l_Lean_Format_isNil(x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_399);
lean_ctor_set_uint8(x_409, sizeof(void*)*2, x_391);
x_410 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set_uint8(x_410, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_379;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_410);
if (lean_is_scalar(x_376)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_376;
}
lean_ctor_set(x_412, 0, x_405);
lean_ctor_set(x_412, 1, x_411);
x_7 = x_13;
x_8 = x_412;
goto _start;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_404);
lean_ctor_set_uint8(x_414, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_379;
}
lean_ctor_set(x_415, 0, x_406);
lean_ctor_set(x_415, 1, x_414);
if (lean_is_scalar(x_376)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_376;
}
lean_ctor_set(x_416, 0, x_405);
lean_ctor_set(x_416, 1, x_415);
x_7 = x_13;
x_8 = x_416;
goto _start;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_418 = lean_ctor_get(x_377, 0);
lean_inc(x_418);
lean_dec(x_377);
x_419 = l_Lean_Format_flatten___main___closed__1;
x_420 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_375, x_419);
x_421 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_422 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
lean_ctor_set_uint8(x_422, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_423 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_418);
x_424 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_424, 0, x_399);
lean_ctor_set(x_424, 1, x_423);
lean_ctor_set_uint8(x_424, sizeof(void*)*2, x_391);
x_425 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_425, 0, x_401);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_426, 0, x_422);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set_uint8(x_426, sizeof(void*)*2, x_391);
x_427 = lean_format_group(x_426);
x_428 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_428, 0, x_407);
lean_ctor_set(x_428, 1, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*2, x_391);
x_429 = l_Lean_Format_isNil(x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_399);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_391);
x_431 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_404);
lean_ctor_set_uint8(x_431, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_379;
}
lean_ctor_set(x_432, 0, x_406);
lean_ctor_set(x_432, 1, x_431);
if (lean_is_scalar(x_376)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_376;
}
lean_ctor_set(x_433, 0, x_405);
lean_ctor_set(x_433, 1, x_432);
x_7 = x_13;
x_8 = x_433;
goto _start;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_435, 0, x_428);
lean_ctor_set(x_435, 1, x_404);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_379;
}
lean_ctor_set(x_436, 0, x_406);
lean_ctor_set(x_436, 1, x_435);
if (lean_is_scalar(x_376)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_376;
}
lean_ctor_set(x_437, 0, x_405);
lean_ctor_set(x_437, 1, x_436);
x_7 = x_13;
x_8 = x_437;
goto _start;
}
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
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_17, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 3);
lean_inc(x_23);
lean_dec(x_17);
lean_inc(x_2);
x_24 = l_Lean_MetavarContext_instantiateMVars(x_2, x_23);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_11, 0, x_26);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_28);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_11, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_15, 1, x_32);
lean_ctor_set(x_15, 0, x_31);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_11);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_expr_eqv(x_38, x_35);
if (x_39 == 0)
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lean_Format_isNil(x_21);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_20, 0, x_35);
if (x_40 == 0)
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_21);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_43);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_45);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = l_Lean_Format_flatten___main___closed__1;
x_48 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_47);
x_49 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_50 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_43);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_38);
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_43);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_43);
x_56 = lean_format_group(x_55);
x_57 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_43);
lean_ctor_set(x_24, 1, x_57);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = l_Lean_Format_flatten___main___closed__1;
x_61 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_60);
x_62 = 0;
x_63 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_64 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_62);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_38);
x_66 = lean_box(1);
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_62);
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*2, x_62);
x_71 = lean_format_group(x_70);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_21);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_62);
lean_ctor_set(x_24, 1, x_72);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_38);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_22);
lean_ctor_set(x_74, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_74);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_20, 0);
lean_inc(x_76);
lean_dec(x_20);
x_77 = lean_expr_eqv(x_76, x_35);
if (x_77 == 0)
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = l_Lean_Format_isNil(x_21);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_22);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_35);
if (x_78 == 0)
{
uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_box(1);
x_84 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_84, 0, x_21);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_82);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_76);
lean_ctor_set(x_24, 1, x_84);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = l_Lean_Format_flatten___main___closed__1;
x_87 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_86);
x_88 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_89 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_82);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_76);
x_91 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*2, x_82);
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_82);
x_95 = lean_format_group(x_94);
x_96 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_82);
lean_ctor_set(x_24, 1, x_96);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_76);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_99 = l_Lean_Format_flatten___main___closed__1;
x_100 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_99);
x_101 = 0;
x_102 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_103 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*2, x_101);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_104 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_76);
x_105 = lean_box(1);
x_106 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_101);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_101);
x_110 = lean_format_group(x_109);
x_111 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_111, 0, x_21);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_101);
lean_ctor_set(x_24, 1, x_111);
lean_ctor_set(x_24, 0, x_81);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_80);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_76);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_22);
lean_ctor_set(x_113, 1, x_18);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_114);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_113);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_24, 0);
lean_inc(x_116);
lean_dec(x_24);
x_117 = lean_ctor_get(x_20, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_118 = x_20;
} else {
 lean_dec_ref(x_20);
 x_118 = lean_box(0);
}
x_119 = lean_expr_eqv(x_117, x_116);
if (x_119 == 0)
{
uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = l_Lean_Format_isNil(x_21);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_22);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_116);
if (x_120 == 0)
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; 
x_124 = 0;
x_125 = lean_box(1);
x_126 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_126, 0, x_21);
lean_ctor_set(x_126, 1, x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_124);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_127; 
lean_dec(x_117);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_15, 1, x_127);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_129 = l_Lean_Format_flatten___main___closed__1;
x_130 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_129);
x_131 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_132 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set_uint8(x_132, sizeof(void*)*2, x_124);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_133 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_117);
x_134 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*2, x_124);
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
x_137 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_124);
x_138 = lean_format_group(x_137);
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_124);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_15, 1, x_140);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_142; 
lean_dec(x_117);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_123);
lean_ctor_set(x_142, 1, x_21);
lean_ctor_set(x_15, 1, x_142);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_144 = l_Lean_Format_flatten___main___closed__1;
x_145 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_144);
x_146 = 0;
x_147 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_148 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_146);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_149 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_117);
x_150 = lean_box(1);
x_151 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
lean_ctor_set_uint8(x_151, sizeof(void*)*2, x_146);
x_152 = lean_unsigned_to_nat(2u);
x_153 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_146);
x_155 = lean_format_group(x_154);
x_156 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_156, 0, x_21);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_146);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_123);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_15, 1, x_157);
lean_ctor_set(x_15, 0, x_122);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_117);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_22);
lean_ctor_set(x_159, 1, x_18);
if (lean_is_scalar(x_118)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_118;
}
lean_ctor_set(x_160, 0, x_116);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_21);
lean_ctor_set(x_15, 1, x_161);
lean_ctor_set(x_15, 0, x_159);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_15, 0);
x_164 = lean_ctor_get(x_15, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_15);
x_165 = lean_ctor_get(x_17, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_17, 3);
lean_inc(x_166);
lean_dec(x_17);
lean_inc(x_2);
x_167 = l_Lean_MetavarContext_instantiateMVars(x_2, x_166);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_165);
lean_ctor_set(x_170, 1, x_18);
lean_ctor_set(x_11, 0, x_168);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_11);
lean_ctor_set(x_171, 1, x_164);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_7 = x_13;
x_8 = x_172;
goto _start;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_free_object(x_11);
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_175 = x_167;
} else {
 lean_dec_ref(x_167);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_163, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_177 = x_163;
} else {
 lean_dec_ref(x_163);
 x_177 = lean_box(0);
}
x_178 = lean_expr_eqv(x_176, x_174);
if (x_178 == 0)
{
uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = l_Lean_Format_isNil(x_164);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_165);
lean_ctor_set(x_181, 1, x_180);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_174);
if (x_179 == 0)
{
uint8_t x_183; lean_object* x_184; lean_object* x_185; 
x_183 = 0;
x_184 = lean_box(1);
x_185 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_185, 0, x_164);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*2, x_183);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_176);
if (lean_is_scalar(x_175)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_175;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_186);
x_7 = x_13;
x_8 = x_187;
goto _start;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = l_Lean_Format_flatten___main___closed__1;
x_190 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_189);
x_191 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_192 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*2, x_183);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_193 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_176);
x_194 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_194, 0, x_184);
lean_ctor_set(x_194, 1, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*2, x_183);
x_195 = lean_unsigned_to_nat(2u);
x_196 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_183);
x_198 = lean_format_group(x_197);
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_183);
if (lean_is_scalar(x_175)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_175;
}
lean_ctor_set(x_200, 0, x_182);
lean_ctor_set(x_200, 1, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_181);
lean_ctor_set(x_201, 1, x_200);
x_7 = x_13;
x_8 = x_201;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_176);
if (lean_is_scalar(x_175)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_175;
}
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_164);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_181);
lean_ctor_set(x_204, 1, x_203);
x_7 = x_13;
x_8 = x_204;
goto _start;
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_206 = l_Lean_Format_flatten___main___closed__1;
x_207 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_18, x_206);
x_208 = 0;
x_209 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_210 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_208);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_211 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_176);
x_212 = lean_box(1);
x_213 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*2, x_208);
x_214 = lean_unsigned_to_nat(2u);
x_215 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_216, 0, x_210);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set_uint8(x_216, sizeof(void*)*2, x_208);
x_217 = lean_format_group(x_216);
x_218 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_218, 0, x_164);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*2, x_208);
if (lean_is_scalar(x_175)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_175;
}
lean_ctor_set(x_219, 0, x_182);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_181);
lean_ctor_set(x_220, 1, x_219);
x_7 = x_13;
x_8 = x_220;
goto _start;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_176);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_165);
lean_ctor_set(x_222, 1, x_18);
if (lean_is_scalar(x_177)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_177;
}
lean_ctor_set(x_223, 0, x_174);
if (lean_is_scalar(x_175)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_175;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_164);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_7 = x_13;
x_8 = x_225;
goto _start;
}
}
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_free_object(x_11);
x_227 = lean_ctor_get(x_8, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_228 = x_8;
} else {
 lean_dec_ref(x_8);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_15, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_15, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_231 = x_15;
} else {
 lean_dec_ref(x_15);
 x_231 = lean_box(0);
}
x_232 = lean_ctor_get(x_17, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_17, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_17, 4);
lean_inc(x_234);
lean_dec(x_17);
x_235 = l_Lean_Format_isNil(x_230);
lean_inc(x_2);
x_236 = l_Lean_MetavarContext_instantiateMVars(x_2, x_233);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
lean_inc(x_2);
x_238 = l_Lean_MetavarContext_instantiateMVars(x_2, x_234);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec(x_238);
x_240 = l_Lean_Name_toString___closed__1;
x_241 = l_Lean_Name_toStringWithSep___main(x_240, x_232);
x_242 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_243 = 0;
x_244 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_245 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_246 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_237);
x_247 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
lean_ctor_set_uint8(x_247, sizeof(void*)*2, x_243);
x_248 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_249 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
lean_ctor_set_uint8(x_249, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_250 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_239);
x_251 = lean_box(1);
x_252 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
lean_ctor_set_uint8(x_252, sizeof(void*)*2, x_243);
x_253 = lean_unsigned_to_nat(2u);
x_254 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_252);
x_255 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_255, 0, x_249);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*2, x_243);
x_256 = lean_format_group(x_255);
x_257 = lean_box(0);
x_258 = lean_box(0);
if (x_235 == 0)
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_292, 0, x_230);
lean_ctor_set(x_292, 1, x_251);
lean_ctor_set_uint8(x_292, sizeof(void*)*2, x_243);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_293; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
x_293 = l_Lean_Format_isNil(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_294 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_251);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_243);
x_295 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_256);
lean_ctor_set_uint8(x_295, sizeof(void*)*2, x_243);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_258);
lean_ctor_set(x_296, 1, x_295);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_257);
lean_ctor_set(x_297, 1, x_296);
x_7 = x_13;
x_8 = x_297;
goto _start;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_299, 0, x_292);
lean_ctor_set(x_299, 1, x_256);
lean_ctor_set_uint8(x_299, sizeof(void*)*2, x_243);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_258);
lean_ctor_set(x_300, 1, x_299);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_257);
lean_ctor_set(x_301, 1, x_300);
x_7 = x_13;
x_8 = x_301;
goto _start;
}
}
else
{
x_259 = x_292;
goto block_291;
}
}
else
{
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_230);
lean_ctor_set(x_303, 1, x_256);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_243);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_258);
lean_ctor_set(x_304, 1, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_257);
lean_ctor_set(x_305, 1, x_304);
x_7 = x_13;
x_8 = x_305;
goto _start;
}
else
{
x_259 = x_230;
goto block_291;
}
}
block_291:
{
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_260; 
lean_dec(x_227);
x_260 = l_Lean_Format_isNil(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_251);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_243);
x_262 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
lean_ctor_set_uint8(x_262, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_231;
}
lean_ctor_set(x_263, 0, x_258);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_228)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_228;
}
lean_ctor_set(x_264, 0, x_257);
lean_ctor_set(x_264, 1, x_263);
x_7 = x_13;
x_8 = x_264;
goto _start;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_256);
lean_ctor_set_uint8(x_266, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_231;
}
lean_ctor_set(x_267, 0, x_258);
lean_ctor_set(x_267, 1, x_266);
if (lean_is_scalar(x_228)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_228;
}
lean_ctor_set(x_268, 0, x_257);
lean_ctor_set(x_268, 1, x_267);
x_7 = x_13;
x_8 = x_268;
goto _start;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_270 = lean_ctor_get(x_229, 0);
lean_inc(x_270);
lean_dec(x_229);
x_271 = l_Lean_Format_flatten___main___closed__1;
x_272 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_227, x_271);
x_273 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_243);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_275 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_270);
x_276 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_276, 0, x_251);
lean_ctor_set(x_276, 1, x_275);
lean_ctor_set_uint8(x_276, sizeof(void*)*2, x_243);
x_277 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_277, 0, x_253);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_278, 0, x_274);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*2, x_243);
x_279 = lean_format_group(x_278);
x_280 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_280, 0, x_259);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set_uint8(x_280, sizeof(void*)*2, x_243);
x_281 = l_Lean_Format_isNil(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_251);
lean_ctor_set_uint8(x_282, sizeof(void*)*2, x_243);
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_256);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_231;
}
lean_ctor_set(x_284, 0, x_258);
lean_ctor_set(x_284, 1, x_283);
if (lean_is_scalar(x_228)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_228;
}
lean_ctor_set(x_285, 0, x_257);
lean_ctor_set(x_285, 1, x_284);
x_7 = x_13;
x_8 = x_285;
goto _start;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_287, 0, x_280);
lean_ctor_set(x_287, 1, x_256);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_243);
if (lean_is_scalar(x_231)) {
 x_288 = lean_alloc_ctor(0, 2, 0);
} else {
 x_288 = x_231;
}
lean_ctor_set(x_288, 0, x_258);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_228)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_228;
}
lean_ctor_set(x_289, 0, x_257);
lean_ctor_set(x_289, 1, x_288);
x_7 = x_13;
x_8 = x_289;
goto _start;
}
}
}
}
}
else
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_11, 0);
lean_inc(x_307);
lean_dec(x_11);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_308 = lean_ctor_get(x_8, 0);
lean_inc(x_308);
lean_dec(x_8);
x_309 = lean_ctor_get(x_15, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_15, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_311 = x_15;
} else {
 lean_dec_ref(x_15);
 x_311 = lean_box(0);
}
x_312 = lean_ctor_get(x_307, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_307, 3);
lean_inc(x_313);
lean_dec(x_307);
lean_inc(x_2);
x_314 = l_Lean_MetavarContext_instantiateMVars(x_2, x_313);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_312);
lean_ctor_set(x_317, 1, x_308);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_315);
if (lean_is_scalar(x_316)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_316;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_320 = lean_alloc_ctor(0, 2, 0);
} else {
 x_320 = x_311;
}
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_319);
x_7 = x_13;
x_8 = x_320;
goto _start;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_322 = lean_ctor_get(x_314, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_323 = x_314;
} else {
 lean_dec_ref(x_314);
 x_323 = lean_box(0);
}
x_324 = lean_ctor_get(x_309, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_325 = x_309;
} else {
 lean_dec_ref(x_309);
 x_325 = lean_box(0);
}
x_326 = lean_expr_eqv(x_324, x_322);
if (x_326 == 0)
{
uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = l_Lean_Format_isNil(x_310);
x_328 = lean_box(0);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_312);
lean_ctor_set(x_329, 1, x_328);
if (lean_is_scalar(x_325)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_325;
}
lean_ctor_set(x_330, 0, x_322);
if (x_327 == 0)
{
uint8_t x_331; lean_object* x_332; lean_object* x_333; 
x_331 = 0;
x_332 = lean_box(1);
x_333 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_333, 0, x_310);
lean_ctor_set(x_333, 1, x_332);
lean_ctor_set_uint8(x_333, sizeof(void*)*2, x_331);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_324);
if (lean_is_scalar(x_323)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_323;
}
lean_ctor_set(x_334, 0, x_330);
lean_ctor_set(x_334, 1, x_333);
if (lean_is_scalar(x_311)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_311;
}
lean_ctor_set(x_335, 0, x_329);
lean_ctor_set(x_335, 1, x_334);
x_7 = x_13;
x_8 = x_335;
goto _start;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_337 = l_Lean_Format_flatten___main___closed__1;
x_338 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_337);
x_339 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_340 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
lean_ctor_set_uint8(x_340, sizeof(void*)*2, x_331);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_341 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_324);
x_342 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_342, 0, x_332);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set_uint8(x_342, sizeof(void*)*2, x_331);
x_343 = lean_unsigned_to_nat(2u);
x_344 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_342);
x_345 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_345, 0, x_340);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set_uint8(x_345, sizeof(void*)*2, x_331);
x_346 = lean_format_group(x_345);
x_347 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_347, 0, x_333);
lean_ctor_set(x_347, 1, x_346);
lean_ctor_set_uint8(x_347, sizeof(void*)*2, x_331);
if (lean_is_scalar(x_323)) {
 x_348 = lean_alloc_ctor(0, 2, 0);
} else {
 x_348 = x_323;
}
lean_ctor_set(x_348, 0, x_330);
lean_ctor_set(x_348, 1, x_347);
if (lean_is_scalar(x_311)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_311;
}
lean_ctor_set(x_349, 0, x_329);
lean_ctor_set(x_349, 1, x_348);
x_7 = x_13;
x_8 = x_349;
goto _start;
}
}
else
{
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_324);
if (lean_is_scalar(x_323)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_323;
}
lean_ctor_set(x_351, 0, x_330);
lean_ctor_set(x_351, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_352 = lean_alloc_ctor(0, 2, 0);
} else {
 x_352 = x_311;
}
lean_ctor_set(x_352, 0, x_329);
lean_ctor_set(x_352, 1, x_351);
x_7 = x_13;
x_8 = x_352;
goto _start;
}
else
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_354 = l_Lean_Format_flatten___main___closed__1;
x_355 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_308, x_354);
x_356 = 0;
x_357 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_358 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*2, x_356);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_359 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_324);
x_360 = lean_box(1);
x_361 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*2, x_356);
x_362 = lean_unsigned_to_nat(2u);
x_363 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_363, 1, x_361);
x_364 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*2, x_356);
x_365 = lean_format_group(x_364);
x_366 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_366, 0, x_310);
lean_ctor_set(x_366, 1, x_365);
lean_ctor_set_uint8(x_366, sizeof(void*)*2, x_356);
if (lean_is_scalar(x_323)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_323;
}
lean_ctor_set(x_367, 0, x_330);
lean_ctor_set(x_367, 1, x_366);
if (lean_is_scalar(x_311)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_311;
}
lean_ctor_set(x_368, 0, x_329);
lean_ctor_set(x_368, 1, x_367);
x_7 = x_13;
x_8 = x_368;
goto _start;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_324);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_312);
lean_ctor_set(x_370, 1, x_308);
if (lean_is_scalar(x_325)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_325;
}
lean_ctor_set(x_371, 0, x_322);
if (lean_is_scalar(x_323)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_323;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_310);
if (lean_is_scalar(x_311)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_311;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_372);
x_7 = x_13;
x_8 = x_373;
goto _start;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_375 = lean_ctor_get(x_8, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_376 = x_8;
} else {
 lean_dec_ref(x_8);
 x_376 = lean_box(0);
}
x_377 = lean_ctor_get(x_15, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_15, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_379 = x_15;
} else {
 lean_dec_ref(x_15);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_307, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_307, 3);
lean_inc(x_381);
x_382 = lean_ctor_get(x_307, 4);
lean_inc(x_382);
lean_dec(x_307);
x_383 = l_Lean_Format_isNil(x_378);
lean_inc(x_2);
x_384 = l_Lean_MetavarContext_instantiateMVars(x_2, x_381);
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec(x_384);
lean_inc(x_2);
x_386 = l_Lean_MetavarContext_instantiateMVars(x_2, x_382);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_Lean_Name_toString___closed__1;
x_389 = l_Lean_Name_toStringWithSep___main(x_388, x_380);
x_390 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_390, 0, x_389);
x_391 = 0;
x_392 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_393 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_392);
lean_ctor_set_uint8(x_393, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_394 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_385);
x_395 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set_uint8(x_395, sizeof(void*)*2, x_391);
x_396 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_397 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
lean_ctor_set_uint8(x_397, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_398 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_387);
x_399 = lean_box(1);
x_400 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*2, x_391);
x_401 = lean_unsigned_to_nat(2u);
x_402 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_403, 0, x_397);
lean_ctor_set(x_403, 1, x_402);
lean_ctor_set_uint8(x_403, sizeof(void*)*2, x_391);
x_404 = lean_format_group(x_403);
x_405 = lean_box(0);
x_406 = lean_box(0);
if (x_383 == 0)
{
lean_object* x_440; 
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_378);
lean_ctor_set(x_440, 1, x_399);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_391);
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_441; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_376);
x_441 = l_Lean_Format_isNil(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_399);
lean_ctor_set_uint8(x_442, sizeof(void*)*2, x_391);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_404);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_391);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_406);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_405);
lean_ctor_set(x_445, 1, x_444);
x_7 = x_13;
x_8 = x_445;
goto _start;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_447, 0, x_440);
lean_ctor_set(x_447, 1, x_404);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_391);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_406);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_405);
lean_ctor_set(x_449, 1, x_448);
x_7 = x_13;
x_8 = x_449;
goto _start;
}
}
else
{
x_407 = x_440;
goto block_439;
}
}
else
{
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_379);
lean_dec(x_377);
lean_dec(x_376);
x_451 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_451, 0, x_378);
lean_ctor_set(x_451, 1, x_404);
lean_ctor_set_uint8(x_451, sizeof(void*)*2, x_391);
x_452 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_452, 0, x_406);
lean_ctor_set(x_452, 1, x_451);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_405);
lean_ctor_set(x_453, 1, x_452);
x_7 = x_13;
x_8 = x_453;
goto _start;
}
else
{
x_407 = x_378;
goto block_439;
}
}
block_439:
{
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_408; 
lean_dec(x_375);
x_408 = l_Lean_Format_isNil(x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_399);
lean_ctor_set_uint8(x_409, sizeof(void*)*2, x_391);
x_410 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_404);
lean_ctor_set_uint8(x_410, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_379;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_410);
if (lean_is_scalar(x_376)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_376;
}
lean_ctor_set(x_412, 0, x_405);
lean_ctor_set(x_412, 1, x_411);
x_7 = x_13;
x_8 = x_412;
goto _start;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_414, 0, x_407);
lean_ctor_set(x_414, 1, x_404);
lean_ctor_set_uint8(x_414, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_379;
}
lean_ctor_set(x_415, 0, x_406);
lean_ctor_set(x_415, 1, x_414);
if (lean_is_scalar(x_376)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_376;
}
lean_ctor_set(x_416, 0, x_405);
lean_ctor_set(x_416, 1, x_415);
x_7 = x_13;
x_8 = x_416;
goto _start;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_418 = lean_ctor_get(x_377, 0);
lean_inc(x_418);
lean_dec(x_377);
x_419 = l_Lean_Format_flatten___main___closed__1;
x_420 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_375, x_419);
x_421 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_422 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
lean_ctor_set_uint8(x_422, sizeof(void*)*2, x_391);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_423 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_418);
x_424 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_424, 0, x_399);
lean_ctor_set(x_424, 1, x_423);
lean_ctor_set_uint8(x_424, sizeof(void*)*2, x_391);
x_425 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_425, 0, x_401);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_426, 0, x_422);
lean_ctor_set(x_426, 1, x_425);
lean_ctor_set_uint8(x_426, sizeof(void*)*2, x_391);
x_427 = lean_format_group(x_426);
x_428 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_428, 0, x_407);
lean_ctor_set(x_428, 1, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*2, x_391);
x_429 = l_Lean_Format_isNil(x_428);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_430 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set(x_430, 1, x_399);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_391);
x_431 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_404);
lean_ctor_set_uint8(x_431, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_379;
}
lean_ctor_set(x_432, 0, x_406);
lean_ctor_set(x_432, 1, x_431);
if (lean_is_scalar(x_376)) {
 x_433 = lean_alloc_ctor(0, 2, 0);
} else {
 x_433 = x_376;
}
lean_ctor_set(x_433, 0, x_405);
lean_ctor_set(x_433, 1, x_432);
x_7 = x_13;
x_8 = x_433;
goto _start;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_435, 0, x_428);
lean_ctor_set(x_435, 1, x_404);
lean_ctor_set_uint8(x_435, sizeof(void*)*2, x_391);
if (lean_is_scalar(x_379)) {
 x_436 = lean_alloc_ctor(0, 2, 0);
} else {
 x_436 = x_379;
}
lean_ctor_set(x_436, 0, x_406);
lean_ctor_set(x_436, 1, x_435);
if (lean_is_scalar(x_376)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_376;
}
lean_ctor_set(x_437, 0, x_405);
lean_ctor_set(x_437, 1, x_436);
x_7 = x_13;
x_8 = x_437;
goto _start;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_17 = lean_ctor_get(x_8, 2);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
lean_dec(x_8);
if (x_16 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_60 = 0;
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_62, 0, x_15);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_60);
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = x_62;
goto block_59;
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
x_22 = x_62;
goto block_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_14, 0);
lean_inc(x_63);
lean_dec(x_14);
x_64 = l_Lean_Format_flatten___main___closed__1;
x_65 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_13, x_64);
x_66 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_60);
x_68 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_63);
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_60);
x_70 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_70, 0, x_19);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_60);
x_72 = lean_format_group(x_71);
x_73 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_73, 0, x_62);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_60);
x_22 = x_73;
goto block_59;
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
x_22 = x_15;
goto block_59;
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
x_22 = x_15;
goto block_59;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_74 = lean_ctor_get(x_14, 0);
lean_inc(x_74);
lean_dec(x_14);
x_75 = l_Lean_Format_flatten___main___closed__1;
x_76 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_13, x_75);
x_77 = 0;
x_78 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_79 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_77);
x_80 = l_Lean_ppExpr(x_1, x_2, x_3, x_4, x_74);
x_81 = lean_box(1);
x_82 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set_uint8(x_82, sizeof(void*)*2, x_77);
x_83 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_83, 0, x_19);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_77);
x_85 = lean_format_group(x_84);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_15);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_77);
x_22 = x_86;
goto block_59;
}
}
}
block_59:
{
uint8_t x_23; 
x_23 = l_Lean_Format_isNil(x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = 0;
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_24);
x_27 = l_Lean_ppGoal___closed__6;
x_28 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_24);
x_29 = l_Lean_Format_flatten___main___closed__1;
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_24);
x_31 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_24);
if (lean_obj_tag(x_21) == 0)
{
return x_31;
}
else
{
lean_object* x_41; 
x_41 = lean_box(0);
x_32 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_21);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_ppGoal___closed__8;
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_24);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_24);
x_39 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set_uint8(x_39, sizeof(void*)*2, x_24);
return x_39;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = 0;
x_43 = l_Lean_ppGoal___closed__6;
x_44 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_44, 0, x_22);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_42);
x_45 = l_Lean_Format_flatten___main___closed__1;
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_42);
x_47 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_20);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_42);
if (lean_obj_tag(x_21) == 0)
{
return x_47;
}
else
{
lean_object* x_58; 
x_58 = lean_box(0);
x_48 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_49 = l_Lean_Name_toString___closed__1;
x_50 = l_Lean_Name_toStringWithSep___main(x_49, x_21);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_ppGoal___closed__8;
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_42);
x_54 = lean_box(1);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_42);
x_56 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_47);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_42);
return x_56;
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
