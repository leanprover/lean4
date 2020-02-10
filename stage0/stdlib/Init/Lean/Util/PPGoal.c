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
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
lean_object* l_Lean_MetavarContext_instantiateMVars(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__2;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_PersistentArray_foldlM___at_Lean_ppGoal___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppGoal___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = l_List_reverse___rarg(x_18);
x_48 = l_Lean_Format_flatten___main___closed__1;
x_49 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_47, x_48);
x_50 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_43);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_43);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_43);
x_57 = lean_format_group(x_56);
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_43);
lean_ctor_set(x_24, 1, x_58);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = l_List_reverse___rarg(x_18);
x_62 = l_Lean_Format_flatten___main___closed__1;
x_63 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_61, x_62);
x_64 = 0;
x_65 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_64);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_67 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_68 = lean_box(1);
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_64);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_64);
x_73 = lean_format_group(x_72);
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_64);
lean_ctor_set(x_24, 1, x_74);
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
lean_object* x_76; 
lean_dec(x_38);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_22);
lean_ctor_set(x_76, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_76);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
lean_dec(x_20);
x_79 = lean_expr_eqv(x_78, x_35);
if (x_79 == 0)
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = l_Lean_Format_isNil(x_21);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_22);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_35);
if (x_80 == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_84 = 0;
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_21);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_84);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_78);
lean_ctor_set(x_24, 1, x_86);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = l_List_reverse___rarg(x_18);
x_89 = l_Lean_Format_flatten___main___closed__1;
x_90 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_88, x_89);
x_91 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_92 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_84);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_93 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_78);
x_94 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_84);
x_95 = lean_unsigned_to_nat(2u);
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_84);
x_98 = lean_format_group(x_97);
x_99 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_84);
lean_ctor_set(x_24, 1, x_99);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_78);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = l_List_reverse___rarg(x_18);
x_103 = l_Lean_Format_flatten___main___closed__1;
x_104 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_102, x_103);
x_105 = 0;
x_106 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_107 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_105);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_108 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_78);
x_109 = lean_box(1);
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_105);
x_114 = lean_format_group(x_113);
x_115 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_115, 0, x_21);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_105);
lean_ctor_set(x_24, 1, x_115);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_78);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_22);
lean_ctor_set(x_117, 1, x_18);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_118);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_117);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_24, 0);
lean_inc(x_120);
lean_dec(x_24);
x_121 = lean_ctor_get(x_20, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_122 = x_20;
} else {
 lean_dec_ref(x_20);
 x_122 = lean_box(0);
}
x_123 = lean_expr_eqv(x_121, x_120);
if (x_123 == 0)
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Lean_Format_isNil(x_21);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_22);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_120);
if (x_124 == 0)
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_128 = 0;
x_129 = lean_box(1);
x_130 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_130, 0, x_21);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_128);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_131; 
lean_dec(x_121);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_15, 1, x_131);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = l_List_reverse___rarg(x_18);
x_134 = l_Lean_Format_flatten___main___closed__1;
x_135 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_133, x_134);
x_136 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_137 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_128);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_138 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_121);
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_128);
x_140 = lean_unsigned_to_nat(2u);
x_141 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_128);
x_143 = lean_format_group(x_142);
x_144 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_128);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_127);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_15, 1, x_145);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_147; 
lean_dec(x_121);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_127);
lean_ctor_set(x_147, 1, x_21);
lean_ctor_set(x_15, 1, x_147);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_149 = l_List_reverse___rarg(x_18);
x_150 = l_Lean_Format_flatten___main___closed__1;
x_151 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_149, x_150);
x_152 = 0;
x_153 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_154 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_152);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_155 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_121);
x_156 = lean_box(1);
x_157 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*2, x_152);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_152);
x_161 = lean_format_group(x_160);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_21);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_152);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_127);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_15, 1, x_163);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_121);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_22);
lean_ctor_set(x_165, 1, x_18);
if (lean_is_scalar(x_122)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_122;
}
lean_ctor_set(x_166, 0, x_120);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_21);
lean_ctor_set(x_15, 1, x_167);
lean_ctor_set(x_15, 0, x_165);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_15, 0);
x_170 = lean_ctor_get(x_15, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_15);
x_171 = lean_ctor_get(x_17, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_17, 3);
lean_inc(x_172);
lean_dec(x_17);
lean_inc(x_2);
x_173 = l_Lean_MetavarContext_instantiateMVars(x_2, x_172);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_18);
lean_ctor_set(x_11, 0, x_174);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_11);
lean_ctor_set(x_177, 1, x_170);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_7 = x_13;
x_8 = x_178;
goto _start;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_free_object(x_11);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_181 = x_173;
} else {
 lean_dec_ref(x_173);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_169, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_183 = x_169;
} else {
 lean_dec_ref(x_169);
 x_183 = lean_box(0);
}
x_184 = lean_expr_eqv(x_182, x_180);
if (x_184 == 0)
{
uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l_Lean_Format_isNil(x_170);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_171);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_180);
if (x_185 == 0)
{
uint8_t x_189; lean_object* x_190; lean_object* x_191; 
x_189 = 0;
x_190 = lean_box(1);
x_191 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_191, 0, x_170);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_189);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_182);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_192);
x_7 = x_13;
x_8 = x_193;
goto _start;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_195 = l_List_reverse___rarg(x_18);
x_196 = l_Lean_Format_flatten___main___closed__1;
x_197 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_195, x_196);
x_198 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_189);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_200 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_182);
x_201 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_201, 0, x_190);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_189);
x_202 = lean_unsigned_to_nat(2u);
x_203 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_189);
x_205 = lean_format_group(x_204);
x_206 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_206, 0, x_191);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_189);
if (lean_is_scalar(x_181)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_181;
}
lean_ctor_set(x_207, 0, x_188);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_187);
lean_ctor_set(x_208, 1, x_207);
x_7 = x_13;
x_8 = x_208;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_182);
if (lean_is_scalar(x_181)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_181;
}
lean_ctor_set(x_210, 0, x_188);
lean_ctor_set(x_210, 1, x_170);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_187);
lean_ctor_set(x_211, 1, x_210);
x_7 = x_13;
x_8 = x_211;
goto _start;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_213 = l_List_reverse___rarg(x_18);
x_214 = l_Lean_Format_flatten___main___closed__1;
x_215 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_213, x_214);
x_216 = 0;
x_217 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_218 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*2, x_216);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_219 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_182);
x_220 = lean_box(1);
x_221 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set_uint8(x_221, sizeof(void*)*2, x_216);
x_222 = lean_unsigned_to_nat(2u);
x_223 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_224, 0, x_218);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*2, x_216);
x_225 = lean_format_group(x_224);
x_226 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_226, 0, x_170);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_216);
if (lean_is_scalar(x_181)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_181;
}
lean_ctor_set(x_227, 0, x_188);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_187);
lean_ctor_set(x_228, 1, x_227);
x_7 = x_13;
x_8 = x_228;
goto _start;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_182);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_171);
lean_ctor_set(x_230, 1, x_18);
if (lean_is_scalar(x_183)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_183;
}
lean_ctor_set(x_231, 0, x_180);
if (lean_is_scalar(x_181)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_181;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_170);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_7 = x_13;
x_8 = x_233;
goto _start;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_free_object(x_11);
x_235 = lean_ctor_get(x_8, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_236 = x_8;
} else {
 lean_dec_ref(x_8);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_15, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_15, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_239 = x_15;
} else {
 lean_dec_ref(x_15);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_17, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_17, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_17, 4);
lean_inc(x_242);
lean_dec(x_17);
x_243 = l_Lean_Format_isNil(x_238);
lean_inc(x_2);
x_244 = l_Lean_MetavarContext_instantiateMVars(x_2, x_241);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
lean_inc(x_2);
x_246 = l_Lean_MetavarContext_instantiateMVars(x_2, x_242);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec(x_246);
x_248 = l_Lean_Name_toString___closed__1;
x_249 = l_Lean_Name_toStringWithSep___main(x_248, x_240);
x_250 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_251 = 0;
x_252 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_253 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_254 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_245);
x_255 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*2, x_251);
x_256 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_257 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set_uint8(x_257, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_258 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_247);
x_259 = lean_box(1);
x_260 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set_uint8(x_260, sizeof(void*)*2, x_251);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set_uint8(x_263, sizeof(void*)*2, x_251);
x_264 = lean_format_group(x_263);
x_265 = lean_box(0);
x_266 = lean_box(0);
if (x_243 == 0)
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_301, 0, x_238);
lean_ctor_set(x_301, 1, x_259);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_251);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_302; 
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_236);
x_302 = l_Lean_Format_isNil(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_259);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_251);
x_304 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_264);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_251);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_266);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_265);
lean_ctor_set(x_306, 1, x_305);
x_7 = x_13;
x_8 = x_306;
goto _start;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_308, 0, x_301);
lean_ctor_set(x_308, 1, x_264);
lean_ctor_set_uint8(x_308, sizeof(void*)*2, x_251);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_266);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_265);
lean_ctor_set(x_310, 1, x_309);
x_7 = x_13;
x_8 = x_310;
goto _start;
}
}
else
{
x_267 = x_301;
goto block_300;
}
}
else
{
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_236);
x_312 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_312, 0, x_238);
lean_ctor_set(x_312, 1, x_264);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_251);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_266);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_265);
lean_ctor_set(x_314, 1, x_313);
x_7 = x_13;
x_8 = x_314;
goto _start;
}
else
{
x_267 = x_238;
goto block_300;
}
}
block_300:
{
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_268; 
lean_dec(x_235);
x_268 = l_Lean_Format_isNil(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_251);
x_270 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_264);
lean_ctor_set_uint8(x_270, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_239;
}
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set(x_271, 1, x_270);
if (lean_is_scalar(x_236)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_236;
}
lean_ctor_set(x_272, 0, x_265);
lean_ctor_set(x_272, 1, x_271);
x_7 = x_13;
x_8 = x_272;
goto _start;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_264);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_239;
}
lean_ctor_set(x_275, 0, x_266);
lean_ctor_set(x_275, 1, x_274);
if (lean_is_scalar(x_236)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_236;
}
lean_ctor_set(x_276, 0, x_265);
lean_ctor_set(x_276, 1, x_275);
x_7 = x_13;
x_8 = x_276;
goto _start;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_278 = lean_ctor_get(x_237, 0);
lean_inc(x_278);
lean_dec(x_237);
x_279 = l_List_reverse___rarg(x_235);
x_280 = l_Lean_Format_flatten___main___closed__1;
x_281 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_279, x_280);
x_282 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_284 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_278);
x_285 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_285, 0, x_259);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_251);
x_286 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_286, 0, x_261);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_287, 0, x_283);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_251);
x_288 = lean_format_group(x_287);
x_289 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_289, 0, x_267);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*2, x_251);
x_290 = l_Lean_Format_isNil(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_259);
lean_ctor_set_uint8(x_291, sizeof(void*)*2, x_251);
x_292 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_264);
lean_ctor_set_uint8(x_292, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_239;
}
lean_ctor_set(x_293, 0, x_266);
lean_ctor_set(x_293, 1, x_292);
if (lean_is_scalar(x_236)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_236;
}
lean_ctor_set(x_294, 0, x_265);
lean_ctor_set(x_294, 1, x_293);
x_7 = x_13;
x_8 = x_294;
goto _start;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_264);
lean_ctor_set_uint8(x_296, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_239;
}
lean_ctor_set(x_297, 0, x_266);
lean_ctor_set(x_297, 1, x_296);
if (lean_is_scalar(x_236)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_236;
}
lean_ctor_set(x_298, 0, x_265);
lean_ctor_set(x_298, 1, x_297);
x_7 = x_13;
x_8 = x_298;
goto _start;
}
}
}
}
}
else
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_11, 0);
lean_inc(x_316);
lean_dec(x_11);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_8, 0);
lean_inc(x_317);
lean_dec(x_8);
x_318 = lean_ctor_get(x_15, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_15, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_320 = x_15;
} else {
 lean_dec_ref(x_15);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_316, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 3);
lean_inc(x_322);
lean_dec(x_316);
lean_inc(x_2);
x_323 = l_Lean_MetavarContext_instantiateMVars(x_2, x_322);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_317);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_324);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_320;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_328);
x_7 = x_13;
x_8 = x_329;
goto _start;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_323, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_332 = x_323;
} else {
 lean_dec_ref(x_323);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_334 = x_318;
} else {
 lean_dec_ref(x_318);
 x_334 = lean_box(0);
}
x_335 = lean_expr_eqv(x_333, x_331);
if (x_335 == 0)
{
uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = l_Lean_Format_isNil(x_319);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_321);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_334;
}
lean_ctor_set(x_339, 0, x_331);
if (x_336 == 0)
{
uint8_t x_340; lean_object* x_341; lean_object* x_342; 
x_340 = 0;
x_341 = lean_box(1);
x_342 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_342, 0, x_319);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set_uint8(x_342, sizeof(void*)*2, x_340);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_332;
}
lean_ctor_set(x_343, 0, x_339);
lean_ctor_set(x_343, 1, x_342);
if (lean_is_scalar(x_320)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_320;
}
lean_ctor_set(x_344, 0, x_338);
lean_ctor_set(x_344, 1, x_343);
x_7 = x_13;
x_8 = x_344;
goto _start;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_346 = l_List_reverse___rarg(x_317);
x_347 = l_Lean_Format_flatten___main___closed__1;
x_348 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_346, x_347);
x_349 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_350 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set_uint8(x_350, sizeof(void*)*2, x_340);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_351 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_352 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*2, x_340);
x_353 = lean_unsigned_to_nat(2u);
x_354 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_355, 0, x_350);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_340);
x_356 = lean_format_group(x_355);
x_357 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_357, 0, x_342);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*2, x_340);
if (lean_is_scalar(x_332)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_332;
}
lean_ctor_set(x_358, 0, x_339);
lean_ctor_set(x_358, 1, x_357);
if (lean_is_scalar(x_320)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_320;
}
lean_ctor_set(x_359, 0, x_338);
lean_ctor_set(x_359, 1, x_358);
x_7 = x_13;
x_8 = x_359;
goto _start;
}
}
else
{
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_332;
}
lean_ctor_set(x_361, 0, x_339);
lean_ctor_set(x_361, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_320;
}
lean_ctor_set(x_362, 0, x_338);
lean_ctor_set(x_362, 1, x_361);
x_7 = x_13;
x_8 = x_362;
goto _start;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_364 = l_List_reverse___rarg(x_317);
x_365 = l_Lean_Format_flatten___main___closed__1;
x_366 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_364, x_365);
x_367 = 0;
x_368 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_369 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set_uint8(x_369, sizeof(void*)*2, x_367);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_370 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_371 = lean_box(1);
x_372 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*2, x_367);
x_373 = lean_unsigned_to_nat(2u);
x_374 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_375, 0, x_369);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*2, x_367);
x_376 = lean_format_group(x_375);
x_377 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_377, 0, x_319);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*2, x_367);
if (lean_is_scalar(x_332)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_332;
}
lean_ctor_set(x_378, 0, x_339);
lean_ctor_set(x_378, 1, x_377);
if (lean_is_scalar(x_320)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_320;
}
lean_ctor_set(x_379, 0, x_338);
lean_ctor_set(x_379, 1, x_378);
x_7 = x_13;
x_8 = x_379;
goto _start;
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_333);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_321);
lean_ctor_set(x_381, 1, x_317);
if (lean_is_scalar(x_334)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_334;
}
lean_ctor_set(x_382, 0, x_331);
if (lean_is_scalar(x_332)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_332;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_320;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
x_7 = x_13;
x_8 = x_384;
goto _start;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_386 = lean_ctor_get(x_8, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_387 = x_8;
} else {
 lean_dec_ref(x_8);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_15, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_15, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_390 = x_15;
} else {
 lean_dec_ref(x_15);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_316, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_316, 3);
lean_inc(x_392);
x_393 = lean_ctor_get(x_316, 4);
lean_inc(x_393);
lean_dec(x_316);
x_394 = l_Lean_Format_isNil(x_389);
lean_inc(x_2);
x_395 = l_Lean_MetavarContext_instantiateMVars(x_2, x_392);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
lean_inc(x_2);
x_397 = l_Lean_MetavarContext_instantiateMVars(x_2, x_393);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec(x_397);
x_399 = l_Lean_Name_toString___closed__1;
x_400 = l_Lean_Name_toStringWithSep___main(x_399, x_391);
x_401 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = 0;
x_403 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_404 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set_uint8(x_404, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_405 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_396);
x_406 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*2, x_402);
x_407 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_408 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_409 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_398);
x_410 = lean_box(1);
x_411 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*2, x_402);
x_412 = lean_unsigned_to_nat(2u);
x_413 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_414, 0, x_408);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*2, x_402);
x_415 = lean_format_group(x_414);
x_416 = lean_box(0);
x_417 = lean_box(0);
if (x_394 == 0)
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_452, 0, x_389);
lean_ctor_set(x_452, 1, x_410);
lean_ctor_set_uint8(x_452, sizeof(void*)*2, x_402);
if (lean_obj_tag(x_386) == 0)
{
uint8_t x_453; 
lean_dec(x_390);
lean_dec(x_388);
lean_dec(x_387);
x_453 = l_Lean_Format_isNil(x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_410);
lean_ctor_set_uint8(x_454, sizeof(void*)*2, x_402);
x_455 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_415);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_402);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_417);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_416);
lean_ctor_set(x_457, 1, x_456);
x_7 = x_13;
x_8 = x_457;
goto _start;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_459, 0, x_452);
lean_ctor_set(x_459, 1, x_415);
lean_ctor_set_uint8(x_459, sizeof(void*)*2, x_402);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_417);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_416);
lean_ctor_set(x_461, 1, x_460);
x_7 = x_13;
x_8 = x_461;
goto _start;
}
}
else
{
x_418 = x_452;
goto block_451;
}
}
else
{
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_390);
lean_dec(x_388);
lean_dec(x_387);
x_463 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_463, 0, x_389);
lean_ctor_set(x_463, 1, x_415);
lean_ctor_set_uint8(x_463, sizeof(void*)*2, x_402);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_463);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_416);
lean_ctor_set(x_465, 1, x_464);
x_7 = x_13;
x_8 = x_465;
goto _start;
}
else
{
x_418 = x_389;
goto block_451;
}
}
block_451:
{
if (lean_obj_tag(x_388) == 0)
{
uint8_t x_419; 
lean_dec(x_386);
x_419 = l_Lean_Format_isNil(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_410);
lean_ctor_set_uint8(x_420, sizeof(void*)*2, x_402);
x_421 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_415);
lean_ctor_set_uint8(x_421, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_390;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_421);
if (lean_is_scalar(x_387)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_387;
}
lean_ctor_set(x_423, 0, x_416);
lean_ctor_set(x_423, 1, x_422);
x_7 = x_13;
x_8 = x_423;
goto _start;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_425, 0, x_418);
lean_ctor_set(x_425, 1, x_415);
lean_ctor_set_uint8(x_425, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_390;
}
lean_ctor_set(x_426, 0, x_417);
lean_ctor_set(x_426, 1, x_425);
if (lean_is_scalar(x_387)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_387;
}
lean_ctor_set(x_427, 0, x_416);
lean_ctor_set(x_427, 1, x_426);
x_7 = x_13;
x_8 = x_427;
goto _start;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_429 = lean_ctor_get(x_388, 0);
lean_inc(x_429);
lean_dec(x_388);
x_430 = l_List_reverse___rarg(x_386);
x_431 = l_Lean_Format_flatten___main___closed__1;
x_432 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_430, x_431);
x_433 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_434 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
lean_ctor_set_uint8(x_434, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_435 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_429);
x_436 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_436, 0, x_410);
lean_ctor_set(x_436, 1, x_435);
lean_ctor_set_uint8(x_436, sizeof(void*)*2, x_402);
x_437 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_437, 0, x_412);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_438, 0, x_434);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*2, x_402);
x_439 = lean_format_group(x_438);
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_418);
lean_ctor_set(x_440, 1, x_439);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_402);
x_441 = l_Lean_Format_isNil(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_410);
lean_ctor_set_uint8(x_442, sizeof(void*)*2, x_402);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_415);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_390;
}
lean_ctor_set(x_444, 0, x_417);
lean_ctor_set(x_444, 1, x_443);
if (lean_is_scalar(x_387)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_387;
}
lean_ctor_set(x_445, 0, x_416);
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
lean_ctor_set(x_447, 1, x_415);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_390;
}
lean_ctor_set(x_448, 0, x_417);
lean_ctor_set(x_448, 1, x_447);
if (lean_is_scalar(x_387)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_387;
}
lean_ctor_set(x_449, 0, x_416);
lean_ctor_set(x_449, 1, x_448);
x_7 = x_13;
x_8 = x_449;
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = l_List_reverse___rarg(x_18);
x_48 = l_Lean_Format_flatten___main___closed__1;
x_49 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_47, x_48);
x_50 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_51 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*2, x_43);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_52 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_53 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_43);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*2, x_43);
x_57 = lean_format_group(x_56);
x_58 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_43);
lean_ctor_set(x_24, 1, x_58);
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
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_61 = l_List_reverse___rarg(x_18);
x_62 = l_Lean_Format_flatten___main___closed__1;
x_63 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_61, x_62);
x_64 = 0;
x_65 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_66 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_64);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_67 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_68 = lean_box(1);
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_64);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*2, x_64);
x_73 = lean_format_group(x_72);
x_74 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_64);
lean_ctor_set(x_24, 1, x_74);
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
lean_object* x_76; 
lean_dec(x_38);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_22);
lean_ctor_set(x_76, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_76);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_20, 0);
lean_inc(x_78);
lean_dec(x_20);
x_79 = lean_expr_eqv(x_78, x_35);
if (x_79 == 0)
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = l_Lean_Format_isNil(x_21);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_22);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_35);
if (x_80 == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_84 = 0;
x_85 = lean_box(1);
x_86 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_86, 0, x_21);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_84);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_78);
lean_ctor_set(x_24, 1, x_86);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_88 = l_List_reverse___rarg(x_18);
x_89 = l_Lean_Format_flatten___main___closed__1;
x_90 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_88, x_89);
x_91 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_92 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_84);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_93 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_78);
x_94 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_94, 0, x_85);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_84);
x_95 = lean_unsigned_to_nat(2u);
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_97, 0, x_92);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_84);
x_98 = lean_format_group(x_97);
x_99 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_99, 0, x_86);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_84);
lean_ctor_set(x_24, 1, x_99);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_78);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_102 = l_List_reverse___rarg(x_18);
x_103 = l_Lean_Format_flatten___main___closed__1;
x_104 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_102, x_103);
x_105 = 0;
x_106 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_107 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*2, x_105);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_108 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_78);
x_109 = lean_box(1);
x_110 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*2, x_105);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*2, x_105);
x_114 = lean_format_group(x_113);
x_115 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_115, 0, x_21);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*2, x_105);
lean_ctor_set(x_24, 1, x_115);
lean_ctor_set(x_24, 0, x_83);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_82);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_78);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_22);
lean_ctor_set(x_117, 1, x_18);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_118);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_117);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_24, 0);
lean_inc(x_120);
lean_dec(x_24);
x_121 = lean_ctor_get(x_20, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_122 = x_20;
} else {
 lean_dec_ref(x_20);
 x_122 = lean_box(0);
}
x_123 = lean_expr_eqv(x_121, x_120);
if (x_123 == 0)
{
uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = l_Lean_Format_isNil(x_21);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_22);
lean_ctor_set(x_126, 1, x_125);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_120);
if (x_124 == 0)
{
uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_128 = 0;
x_129 = lean_box(1);
x_130 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_130, 0, x_21);
lean_ctor_set(x_130, 1, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_128);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_131; 
lean_dec(x_121);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_15, 1, x_131);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = l_List_reverse___rarg(x_18);
x_134 = l_Lean_Format_flatten___main___closed__1;
x_135 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_133, x_134);
x_136 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_137 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_128);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_138 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_121);
x_139 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_139, 0, x_129);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*2, x_128);
x_140 = lean_unsigned_to_nat(2u);
x_141 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_uint8(x_142, sizeof(void*)*2, x_128);
x_143 = lean_format_group(x_142);
x_144 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_128);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_127);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_15, 1, x_145);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_147; 
lean_dec(x_121);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_127);
lean_ctor_set(x_147, 1, x_21);
lean_ctor_set(x_15, 1, x_147);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_149 = l_List_reverse___rarg(x_18);
x_150 = l_Lean_Format_flatten___main___closed__1;
x_151 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_149, x_150);
x_152 = 0;
x_153 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_154 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_152);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_155 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_121);
x_156 = lean_box(1);
x_157 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*2, x_152);
x_158 = lean_unsigned_to_nat(2u);
x_159 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_160, 0, x_154);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_uint8(x_160, sizeof(void*)*2, x_152);
x_161 = lean_format_group(x_160);
x_162 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_162, 0, x_21);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_152);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_127);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_15, 1, x_163);
lean_ctor_set(x_15, 0, x_126);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_121);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_22);
lean_ctor_set(x_165, 1, x_18);
if (lean_is_scalar(x_122)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_122;
}
lean_ctor_set(x_166, 0, x_120);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_21);
lean_ctor_set(x_15, 1, x_167);
lean_ctor_set(x_15, 0, x_165);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_15, 0);
x_170 = lean_ctor_get(x_15, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_15);
x_171 = lean_ctor_get(x_17, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_17, 3);
lean_inc(x_172);
lean_dec(x_17);
lean_inc(x_2);
x_173 = l_Lean_MetavarContext_instantiateMVars(x_2, x_172);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_171);
lean_ctor_set(x_176, 1, x_18);
lean_ctor_set(x_11, 0, x_174);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_11);
lean_ctor_set(x_177, 1, x_170);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_7 = x_13;
x_8 = x_178;
goto _start;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_free_object(x_11);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_181 = x_173;
} else {
 lean_dec_ref(x_173);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_169, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_183 = x_169;
} else {
 lean_dec_ref(x_169);
 x_183 = lean_box(0);
}
x_184 = lean_expr_eqv(x_182, x_180);
if (x_184 == 0)
{
uint8_t x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l_Lean_Format_isNil(x_170);
x_186 = lean_box(0);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_171);
lean_ctor_set(x_187, 1, x_186);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(1, 1, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_180);
if (x_185 == 0)
{
uint8_t x_189; lean_object* x_190; lean_object* x_191; 
x_189 = 0;
x_190 = lean_box(1);
x_191 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_191, 0, x_170);
lean_ctor_set(x_191, 1, x_190);
lean_ctor_set_uint8(x_191, sizeof(void*)*2, x_189);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_182);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_187);
lean_ctor_set(x_193, 1, x_192);
x_7 = x_13;
x_8 = x_193;
goto _start;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_195 = l_List_reverse___rarg(x_18);
x_196 = l_Lean_Format_flatten___main___closed__1;
x_197 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_195, x_196);
x_198 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_199 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set_uint8(x_199, sizeof(void*)*2, x_189);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_200 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_182);
x_201 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_201, 0, x_190);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_189);
x_202 = lean_unsigned_to_nat(2u);
x_203 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
x_204 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_203);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_189);
x_205 = lean_format_group(x_204);
x_206 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_206, 0, x_191);
lean_ctor_set(x_206, 1, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_189);
if (lean_is_scalar(x_181)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_181;
}
lean_ctor_set(x_207, 0, x_188);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_187);
lean_ctor_set(x_208, 1, x_207);
x_7 = x_13;
x_8 = x_208;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_182);
if (lean_is_scalar(x_181)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_181;
}
lean_ctor_set(x_210, 0, x_188);
lean_ctor_set(x_210, 1, x_170);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_187);
lean_ctor_set(x_211, 1, x_210);
x_7 = x_13;
x_8 = x_211;
goto _start;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_213 = l_List_reverse___rarg(x_18);
x_214 = l_Lean_Format_flatten___main___closed__1;
x_215 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_213, x_214);
x_216 = 0;
x_217 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_218 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set_uint8(x_218, sizeof(void*)*2, x_216);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_219 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_182);
x_220 = lean_box(1);
x_221 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
lean_ctor_set_uint8(x_221, sizeof(void*)*2, x_216);
x_222 = lean_unsigned_to_nat(2u);
x_223 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_224, 0, x_218);
lean_ctor_set(x_224, 1, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*2, x_216);
x_225 = lean_format_group(x_224);
x_226 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_226, 0, x_170);
lean_ctor_set(x_226, 1, x_225);
lean_ctor_set_uint8(x_226, sizeof(void*)*2, x_216);
if (lean_is_scalar(x_181)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_181;
}
lean_ctor_set(x_227, 0, x_188);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_187);
lean_ctor_set(x_228, 1, x_227);
x_7 = x_13;
x_8 = x_228;
goto _start;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_182);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_171);
lean_ctor_set(x_230, 1, x_18);
if (lean_is_scalar(x_183)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_183;
}
lean_ctor_set(x_231, 0, x_180);
if (lean_is_scalar(x_181)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_181;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_170);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_232);
x_7 = x_13;
x_8 = x_233;
goto _start;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_free_object(x_11);
x_235 = lean_ctor_get(x_8, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_236 = x_8;
} else {
 lean_dec_ref(x_8);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_15, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_15, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_239 = x_15;
} else {
 lean_dec_ref(x_15);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_17, 2);
lean_inc(x_240);
x_241 = lean_ctor_get(x_17, 3);
lean_inc(x_241);
x_242 = lean_ctor_get(x_17, 4);
lean_inc(x_242);
lean_dec(x_17);
x_243 = l_Lean_Format_isNil(x_238);
lean_inc(x_2);
x_244 = l_Lean_MetavarContext_instantiateMVars(x_2, x_241);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
lean_inc(x_2);
x_246 = l_Lean_MetavarContext_instantiateMVars(x_2, x_242);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec(x_246);
x_248 = l_Lean_Name_toString___closed__1;
x_249 = l_Lean_Name_toStringWithSep___main(x_248, x_240);
x_250 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_251 = 0;
x_252 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_253 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_252);
lean_ctor_set_uint8(x_253, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_254 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_245);
x_255 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set_uint8(x_255, sizeof(void*)*2, x_251);
x_256 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_257 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set_uint8(x_257, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_258 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_247);
x_259 = lean_box(1);
x_260 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set_uint8(x_260, sizeof(void*)*2, x_251);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set_uint8(x_263, sizeof(void*)*2, x_251);
x_264 = lean_format_group(x_263);
x_265 = lean_box(0);
x_266 = lean_box(0);
if (x_243 == 0)
{
lean_object* x_301; 
x_301 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_301, 0, x_238);
lean_ctor_set(x_301, 1, x_259);
lean_ctor_set_uint8(x_301, sizeof(void*)*2, x_251);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_302; 
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_236);
x_302 = l_Lean_Format_isNil(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_303 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_259);
lean_ctor_set_uint8(x_303, sizeof(void*)*2, x_251);
x_304 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_264);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_251);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_266);
lean_ctor_set(x_305, 1, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_265);
lean_ctor_set(x_306, 1, x_305);
x_7 = x_13;
x_8 = x_306;
goto _start;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_308, 0, x_301);
lean_ctor_set(x_308, 1, x_264);
lean_ctor_set_uint8(x_308, sizeof(void*)*2, x_251);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_266);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_265);
lean_ctor_set(x_310, 1, x_309);
x_7 = x_13;
x_8 = x_310;
goto _start;
}
}
else
{
x_267 = x_301;
goto block_300;
}
}
else
{
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_236);
x_312 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_312, 0, x_238);
lean_ctor_set(x_312, 1, x_264);
lean_ctor_set_uint8(x_312, sizeof(void*)*2, x_251);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_266);
lean_ctor_set(x_313, 1, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_265);
lean_ctor_set(x_314, 1, x_313);
x_7 = x_13;
x_8 = x_314;
goto _start;
}
else
{
x_267 = x_238;
goto block_300;
}
}
block_300:
{
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_268; 
lean_dec(x_235);
x_268 = l_Lean_Format_isNil(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_251);
x_270 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_264);
lean_ctor_set_uint8(x_270, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_239;
}
lean_ctor_set(x_271, 0, x_266);
lean_ctor_set(x_271, 1, x_270);
if (lean_is_scalar(x_236)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_236;
}
lean_ctor_set(x_272, 0, x_265);
lean_ctor_set(x_272, 1, x_271);
x_7 = x_13;
x_8 = x_272;
goto _start;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_264);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_239;
}
lean_ctor_set(x_275, 0, x_266);
lean_ctor_set(x_275, 1, x_274);
if (lean_is_scalar(x_236)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_236;
}
lean_ctor_set(x_276, 0, x_265);
lean_ctor_set(x_276, 1, x_275);
x_7 = x_13;
x_8 = x_276;
goto _start;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_278 = lean_ctor_get(x_237, 0);
lean_inc(x_278);
lean_dec(x_237);
x_279 = l_List_reverse___rarg(x_235);
x_280 = l_Lean_Format_flatten___main___closed__1;
x_281 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_279, x_280);
x_282 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_283 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set_uint8(x_283, sizeof(void*)*2, x_251);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_284 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_278);
x_285 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_285, 0, x_259);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_251);
x_286 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_286, 0, x_261);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_287, 0, x_283);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*2, x_251);
x_288 = lean_format_group(x_287);
x_289 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_289, 0, x_267);
lean_ctor_set(x_289, 1, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*2, x_251);
x_290 = l_Lean_Format_isNil(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_259);
lean_ctor_set_uint8(x_291, sizeof(void*)*2, x_251);
x_292 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_264);
lean_ctor_set_uint8(x_292, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_239;
}
lean_ctor_set(x_293, 0, x_266);
lean_ctor_set(x_293, 1, x_292);
if (lean_is_scalar(x_236)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_236;
}
lean_ctor_set(x_294, 0, x_265);
lean_ctor_set(x_294, 1, x_293);
x_7 = x_13;
x_8 = x_294;
goto _start;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_296, 0, x_289);
lean_ctor_set(x_296, 1, x_264);
lean_ctor_set_uint8(x_296, sizeof(void*)*2, x_251);
if (lean_is_scalar(x_239)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_239;
}
lean_ctor_set(x_297, 0, x_266);
lean_ctor_set(x_297, 1, x_296);
if (lean_is_scalar(x_236)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_236;
}
lean_ctor_set(x_298, 0, x_265);
lean_ctor_set(x_298, 1, x_297);
x_7 = x_13;
x_8 = x_298;
goto _start;
}
}
}
}
}
else
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_11, 0);
lean_inc(x_316);
lean_dec(x_11);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_317 = lean_ctor_get(x_8, 0);
lean_inc(x_317);
lean_dec(x_8);
x_318 = lean_ctor_get(x_15, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_15, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_320 = x_15;
} else {
 lean_dec_ref(x_15);
 x_320 = lean_box(0);
}
x_321 = lean_ctor_get(x_316, 2);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 3);
lean_inc(x_322);
lean_dec(x_316);
lean_inc(x_2);
x_323 = l_Lean_MetavarContext_instantiateMVars(x_2, x_322);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_325 = x_323;
} else {
 lean_dec_ref(x_323);
 x_325 = lean_box(0);
}
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_321);
lean_ctor_set(x_326, 1, x_317);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_324);
if (lean_is_scalar(x_325)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_325;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_320;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_328);
x_7 = x_13;
x_8 = x_329;
goto _start;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_323, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_332 = x_323;
} else {
 lean_dec_ref(x_323);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_334 = x_318;
} else {
 lean_dec_ref(x_318);
 x_334 = lean_box(0);
}
x_335 = lean_expr_eqv(x_333, x_331);
if (x_335 == 0)
{
uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = l_Lean_Format_isNil(x_319);
x_337 = lean_box(0);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_321);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_334)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_334;
}
lean_ctor_set(x_339, 0, x_331);
if (x_336 == 0)
{
uint8_t x_340; lean_object* x_341; lean_object* x_342; 
x_340 = 0;
x_341 = lean_box(1);
x_342 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_342, 0, x_319);
lean_ctor_set(x_342, 1, x_341);
lean_ctor_set_uint8(x_342, sizeof(void*)*2, x_340);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_332;
}
lean_ctor_set(x_343, 0, x_339);
lean_ctor_set(x_343, 1, x_342);
if (lean_is_scalar(x_320)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_320;
}
lean_ctor_set(x_344, 0, x_338);
lean_ctor_set(x_344, 1, x_343);
x_7 = x_13;
x_8 = x_344;
goto _start;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_346 = l_List_reverse___rarg(x_317);
x_347 = l_Lean_Format_flatten___main___closed__1;
x_348 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_346, x_347);
x_349 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_350 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
lean_ctor_set_uint8(x_350, sizeof(void*)*2, x_340);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_351 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_352 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_352, 0, x_341);
lean_ctor_set(x_352, 1, x_351);
lean_ctor_set_uint8(x_352, sizeof(void*)*2, x_340);
x_353 = lean_unsigned_to_nat(2u);
x_354 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_355, 0, x_350);
lean_ctor_set(x_355, 1, x_354);
lean_ctor_set_uint8(x_355, sizeof(void*)*2, x_340);
x_356 = lean_format_group(x_355);
x_357 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_357, 0, x_342);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*2, x_340);
if (lean_is_scalar(x_332)) {
 x_358 = lean_alloc_ctor(0, 2, 0);
} else {
 x_358 = x_332;
}
lean_ctor_set(x_358, 0, x_339);
lean_ctor_set(x_358, 1, x_357);
if (lean_is_scalar(x_320)) {
 x_359 = lean_alloc_ctor(0, 2, 0);
} else {
 x_359 = x_320;
}
lean_ctor_set(x_359, 0, x_338);
lean_ctor_set(x_359, 1, x_358);
x_7 = x_13;
x_8 = x_359;
goto _start;
}
}
else
{
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_361; lean_object* x_362; 
lean_dec(x_333);
if (lean_is_scalar(x_332)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_332;
}
lean_ctor_set(x_361, 0, x_339);
lean_ctor_set(x_361, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_320;
}
lean_ctor_set(x_362, 0, x_338);
lean_ctor_set(x_362, 1, x_361);
x_7 = x_13;
x_8 = x_362;
goto _start;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_364 = l_List_reverse___rarg(x_317);
x_365 = l_Lean_Format_flatten___main___closed__1;
x_366 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_364, x_365);
x_367 = 0;
x_368 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_369 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set_uint8(x_369, sizeof(void*)*2, x_367);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_370 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_333);
x_371 = lean_box(1);
x_372 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_370);
lean_ctor_set_uint8(x_372, sizeof(void*)*2, x_367);
x_373 = lean_unsigned_to_nat(2u);
x_374 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_375, 0, x_369);
lean_ctor_set(x_375, 1, x_374);
lean_ctor_set_uint8(x_375, sizeof(void*)*2, x_367);
x_376 = lean_format_group(x_375);
x_377 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_377, 0, x_319);
lean_ctor_set(x_377, 1, x_376);
lean_ctor_set_uint8(x_377, sizeof(void*)*2, x_367);
if (lean_is_scalar(x_332)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_332;
}
lean_ctor_set(x_378, 0, x_339);
lean_ctor_set(x_378, 1, x_377);
if (lean_is_scalar(x_320)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_320;
}
lean_ctor_set(x_379, 0, x_338);
lean_ctor_set(x_379, 1, x_378);
x_7 = x_13;
x_8 = x_379;
goto _start;
}
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_333);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_321);
lean_ctor_set(x_381, 1, x_317);
if (lean_is_scalar(x_334)) {
 x_382 = lean_alloc_ctor(1, 1, 0);
} else {
 x_382 = x_334;
}
lean_ctor_set(x_382, 0, x_331);
if (lean_is_scalar(x_332)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_332;
}
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_319);
if (lean_is_scalar(x_320)) {
 x_384 = lean_alloc_ctor(0, 2, 0);
} else {
 x_384 = x_320;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_383);
x_7 = x_13;
x_8 = x_384;
goto _start;
}
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_386 = lean_ctor_get(x_8, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_387 = x_8;
} else {
 lean_dec_ref(x_8);
 x_387 = lean_box(0);
}
x_388 = lean_ctor_get(x_15, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_15, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_390 = x_15;
} else {
 lean_dec_ref(x_15);
 x_390 = lean_box(0);
}
x_391 = lean_ctor_get(x_316, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_316, 3);
lean_inc(x_392);
x_393 = lean_ctor_get(x_316, 4);
lean_inc(x_393);
lean_dec(x_316);
x_394 = l_Lean_Format_isNil(x_389);
lean_inc(x_2);
x_395 = l_Lean_MetavarContext_instantiateMVars(x_2, x_392);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
lean_inc(x_2);
x_397 = l_Lean_MetavarContext_instantiateMVars(x_2, x_393);
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec(x_397);
x_399 = l_Lean_Name_toString___closed__1;
x_400 = l_Lean_Name_toStringWithSep___main(x_399, x_391);
x_401 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_401, 0, x_400);
x_402 = 0;
x_403 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_404 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set_uint8(x_404, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_405 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_396);
x_406 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*2, x_402);
x_407 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_408 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_409 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_398);
x_410 = lean_box(1);
x_411 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*2, x_402);
x_412 = lean_unsigned_to_nat(2u);
x_413 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_414, 0, x_408);
lean_ctor_set(x_414, 1, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*2, x_402);
x_415 = lean_format_group(x_414);
x_416 = lean_box(0);
x_417 = lean_box(0);
if (x_394 == 0)
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_452, 0, x_389);
lean_ctor_set(x_452, 1, x_410);
lean_ctor_set_uint8(x_452, sizeof(void*)*2, x_402);
if (lean_obj_tag(x_386) == 0)
{
uint8_t x_453; 
lean_dec(x_390);
lean_dec(x_388);
lean_dec(x_387);
x_453 = l_Lean_Format_isNil(x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_410);
lean_ctor_set_uint8(x_454, sizeof(void*)*2, x_402);
x_455 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_455, 0, x_454);
lean_ctor_set(x_455, 1, x_415);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_402);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_417);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_416);
lean_ctor_set(x_457, 1, x_456);
x_7 = x_13;
x_8 = x_457;
goto _start;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_459, 0, x_452);
lean_ctor_set(x_459, 1, x_415);
lean_ctor_set_uint8(x_459, sizeof(void*)*2, x_402);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_417);
lean_ctor_set(x_460, 1, x_459);
x_461 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_461, 0, x_416);
lean_ctor_set(x_461, 1, x_460);
x_7 = x_13;
x_8 = x_461;
goto _start;
}
}
else
{
x_418 = x_452;
goto block_451;
}
}
else
{
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_390);
lean_dec(x_388);
lean_dec(x_387);
x_463 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_463, 0, x_389);
lean_ctor_set(x_463, 1, x_415);
lean_ctor_set_uint8(x_463, sizeof(void*)*2, x_402);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_417);
lean_ctor_set(x_464, 1, x_463);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_416);
lean_ctor_set(x_465, 1, x_464);
x_7 = x_13;
x_8 = x_465;
goto _start;
}
else
{
x_418 = x_389;
goto block_451;
}
}
block_451:
{
if (lean_obj_tag(x_388) == 0)
{
uint8_t x_419; 
lean_dec(x_386);
x_419 = l_Lean_Format_isNil(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_420 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_410);
lean_ctor_set_uint8(x_420, sizeof(void*)*2, x_402);
x_421 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_415);
lean_ctor_set_uint8(x_421, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_390;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_421);
if (lean_is_scalar(x_387)) {
 x_423 = lean_alloc_ctor(0, 2, 0);
} else {
 x_423 = x_387;
}
lean_ctor_set(x_423, 0, x_416);
lean_ctor_set(x_423, 1, x_422);
x_7 = x_13;
x_8 = x_423;
goto _start;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_425, 0, x_418);
lean_ctor_set(x_425, 1, x_415);
lean_ctor_set_uint8(x_425, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_426 = lean_alloc_ctor(0, 2, 0);
} else {
 x_426 = x_390;
}
lean_ctor_set(x_426, 0, x_417);
lean_ctor_set(x_426, 1, x_425);
if (lean_is_scalar(x_387)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_387;
}
lean_ctor_set(x_427, 0, x_416);
lean_ctor_set(x_427, 1, x_426);
x_7 = x_13;
x_8 = x_427;
goto _start;
}
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; 
x_429 = lean_ctor_get(x_388, 0);
lean_inc(x_429);
lean_dec(x_388);
x_430 = l_List_reverse___rarg(x_386);
x_431 = l_Lean_Format_flatten___main___closed__1;
x_432 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_430, x_431);
x_433 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_434 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
lean_ctor_set_uint8(x_434, sizeof(void*)*2, x_402);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_435 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_429);
x_436 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_436, 0, x_410);
lean_ctor_set(x_436, 1, x_435);
lean_ctor_set_uint8(x_436, sizeof(void*)*2, x_402);
x_437 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_437, 0, x_412);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_438, 0, x_434);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*2, x_402);
x_439 = lean_format_group(x_438);
x_440 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_440, 0, x_418);
lean_ctor_set(x_440, 1, x_439);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_402);
x_441 = l_Lean_Format_isNil(x_440);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_442 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_410);
lean_ctor_set_uint8(x_442, sizeof(void*)*2, x_402);
x_443 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_415);
lean_ctor_set_uint8(x_443, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_390;
}
lean_ctor_set(x_444, 0, x_417);
lean_ctor_set(x_444, 1, x_443);
if (lean_is_scalar(x_387)) {
 x_445 = lean_alloc_ctor(0, 2, 0);
} else {
 x_445 = x_387;
}
lean_ctor_set(x_445, 0, x_416);
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
lean_ctor_set(x_447, 1, x_415);
lean_ctor_set_uint8(x_447, sizeof(void*)*2, x_402);
if (lean_is_scalar(x_390)) {
 x_448 = lean_alloc_ctor(0, 2, 0);
} else {
 x_448 = x_390;
}
lean_ctor_set(x_448, 0, x_417);
lean_ctor_set(x_448, 1, x_447);
if (lean_is_scalar(x_387)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_387;
}
lean_ctor_set(x_449, 0, x_416);
lean_ctor_set(x_449, 1, x_448);
x_7 = x_13;
x_8 = x_449;
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
lean_object* l_Lean_ppGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_2);
x_5 = lean_metavar_ctx_find_decl(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Lean_ppGoal___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_ppGoal___closed__4;
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_LocalContext_foldlM___at_Lean_ppGoal___spec__2(x_1, x_2, x_3, x_8, x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Format_isNil(x_14);
x_16 = lean_ctor_get(x_7, 2);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
if (x_15 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_61, 0, x_14);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_59);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_61;
goto block_58;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_61;
goto block_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
lean_dec(x_13);
x_63 = l_List_reverse___rarg(x_12);
x_64 = l_Lean_Format_flatten___main___closed__1;
x_65 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_63, x_64);
x_66 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_67 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_59);
x_68 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_62);
x_69 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_59);
x_70 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_70, 0, x_18);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_59);
x_72 = lean_format_group(x_71);
x_73 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_59);
x_21 = x_73;
goto block_58;
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_14;
goto block_58;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_14;
goto block_58;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_13, 0);
lean_inc(x_74);
lean_dec(x_13);
x_75 = l_List_reverse___rarg(x_12);
x_76 = l_Lean_Format_flatten___main___closed__1;
x_77 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_75, x_76);
x_78 = 0;
x_79 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_80 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*2, x_78);
x_81 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_74);
x_82 = lean_box(1);
x_83 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*2, x_78);
x_84 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_84, 0, x_18);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*2, x_78);
x_86 = lean_format_group(x_85);
x_87 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_87, 0, x_14);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_78);
x_21 = x_87;
goto block_58;
}
}
}
block_58:
{
uint8_t x_22; 
x_22 = l_Lean_Format_isNil(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = 0;
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
x_26 = l_Lean_ppGoal___closed__6;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_23);
x_28 = l_Lean_Format_flatten___main___closed__1;
x_29 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_23);
x_30 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set_uint8(x_30, sizeof(void*)*2, x_23);
if (lean_obj_tag(x_20) == 0)
{
return x_30;
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_32 = l_Lean_Name_toString___closed__1;
x_33 = l_Lean_Name_toStringWithSep___main(x_32, x_20);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_ppGoal___closed__8;
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_23);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_24);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_23);
x_38 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
lean_ctor_set_uint8(x_38, sizeof(void*)*2, x_23);
return x_38;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = 0;
x_42 = l_Lean_ppGoal___closed__6;
x_43 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_41);
x_44 = l_Lean_Format_flatten___main___closed__1;
x_45 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*2, x_41);
x_46 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_19);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_41);
if (lean_obj_tag(x_20) == 0)
{
return x_46;
}
else
{
lean_object* x_57; 
x_57 = lean_box(0);
x_47 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_48 = l_Lean_Name_toString___closed__1;
x_49 = l_Lean_Name_toStringWithSep___main(x_48, x_20);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_ppGoal___closed__8;
x_52 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*2, x_41);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*2, x_41);
x_55 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_41);
return x_55;
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
