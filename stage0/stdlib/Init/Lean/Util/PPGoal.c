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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint32_t x_14; uint16_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint16_t x_20; uint8_t x_21; lean_object* x_22; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_9);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
x_14 = 0;
x_15 = 0;
x_16 = 0;
lean_inc(x_2);
x_17 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 6, x_13);
lean_ctor_set_uint32(x_17, sizeof(void*)*2, x_14);
lean_ctor_set_uint16(x_17, sizeof(void*)*2 + 4, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 7, x_16);
x_18 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_4, x_2);
x_19 = 0;
x_20 = 0;
x_21 = 0;
x_22 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 6, x_13);
lean_ctor_set_uint32(x_22, sizeof(void*)*2, x_19);
lean_ctor_set_uint16(x_22, sizeof(void*)*2 + 4, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 7, x_21);
return x_22;
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
uint8_t x_43; lean_object* x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; 
x_43 = 0;
x_44 = lean_box(1);
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_48);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; uint16_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint32_t x_59; uint16_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint32_t x_65; uint16_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; lean_object* x_73; 
x_50 = l_List_reverse___rarg(x_18);
x_51 = l_Lean_Format_flatten___main___closed__1;
x_52 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_50, x_51);
x_53 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_54 = 0;
x_55 = 0;
x_56 = 0;
x_57 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_uint16(x_57, sizeof(void*)*2 + 4, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 7, x_56);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_59 = 0;
x_60 = 0;
x_61 = 0;
x_62 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_62, sizeof(void*)*2, x_59);
lean_ctor_set_uint16(x_62, sizeof(void*)*2 + 4, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 7, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = 0;
x_66 = 0;
x_67 = 0;
x_68 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_uint16(x_68, sizeof(void*)*2 + 4, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 7, x_67);
x_69 = lean_format_group(x_68);
x_70 = 0;
x_71 = 0;
x_72 = 0;
x_73 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_73, 0, x_48);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_73, sizeof(void*)*2, x_70);
lean_ctor_set_uint16(x_73, sizeof(void*)*2 + 4, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 7, x_72);
lean_ctor_set(x_24, 1, x_73);
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint32_t x_81; uint16_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint32_t x_87; uint16_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint32_t x_93; uint16_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; uint16_t x_99; uint8_t x_100; lean_object* x_101; 
x_76 = l_List_reverse___rarg(x_18);
x_77 = l_Lean_Format_flatten___main___closed__1;
x_78 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_76, x_77);
x_79 = 0;
x_80 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_81 = 0;
x_82 = 0;
x_83 = 0;
x_84 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_84, sizeof(void*)*2, x_81);
lean_ctor_set_uint16(x_84, sizeof(void*)*2 + 4, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 7, x_83);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_85 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_86 = lean_box(1);
x_87 = 0;
x_88 = 0;
x_89 = 0;
x_90 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_90, sizeof(void*)*2, x_87);
lean_ctor_set_uint16(x_90, sizeof(void*)*2 + 4, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 7, x_89);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = 0;
x_94 = 0;
x_95 = 0;
x_96 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_96, sizeof(void*)*2, x_93);
lean_ctor_set_uint16(x_96, sizeof(void*)*2 + 4, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 7, x_95);
x_97 = lean_format_group(x_96);
x_98 = 0;
x_99 = 0;
x_100 = 0;
x_101 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_101, 0, x_21);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_101, sizeof(void*)*2, x_98);
lean_ctor_set_uint16(x_101, sizeof(void*)*2 + 4, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 7, x_100);
lean_ctor_set(x_24, 1, x_101);
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
lean_object* x_103; 
lean_dec(x_38);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_22);
lean_ctor_set(x_103, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_103);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_20, 0);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_expr_eqv(x_105, x_35);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = l_Lean_Format_isNil(x_21);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_22);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_35);
if (x_107 == 0)
{
uint8_t x_111; lean_object* x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; lean_object* x_116; 
x_111 = 0;
x_112 = lean_box(1);
x_113 = 0;
x_114 = 0;
x_115 = 0;
x_116 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_116, 0, x_21);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_116, sizeof(void*)*2, x_113);
lean_ctor_set_uint16(x_116, sizeof(void*)*2 + 4, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 7, x_115);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_105);
lean_ctor_set(x_24, 1, x_116);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint32_t x_122; uint16_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; uint16_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint32_t x_133; uint16_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; uint32_t x_138; uint16_t x_139; uint8_t x_140; lean_object* x_141; 
x_118 = l_List_reverse___rarg(x_18);
x_119 = l_Lean_Format_flatten___main___closed__1;
x_120 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_118, x_119);
x_121 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_122 = 0;
x_123 = 0;
x_124 = 0;
x_125 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_125, sizeof(void*)*2, x_122);
lean_ctor_set_uint16(x_125, sizeof(void*)*2 + 4, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 7, x_124);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_105);
x_127 = 0;
x_128 = 0;
x_129 = 0;
x_130 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_130, 0, x_112);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_130, sizeof(void*)*2, x_127);
lean_ctor_set_uint16(x_130, sizeof(void*)*2 + 4, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*2 + 7, x_129);
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = 0;
x_134 = 0;
x_135 = 0;
x_136 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_136, sizeof(void*)*2, x_133);
lean_ctor_set_uint16(x_136, sizeof(void*)*2 + 4, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 7, x_135);
x_137 = lean_format_group(x_136);
x_138 = 0;
x_139 = 0;
x_140 = 0;
x_141 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_141, 0, x_116);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set_uint8(x_141, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_141, sizeof(void*)*2, x_138);
lean_ctor_set_uint16(x_141, sizeof(void*)*2 + 4, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*2 + 7, x_140);
lean_ctor_set(x_24, 1, x_141);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_105);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint32_t x_149; uint16_t x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint32_t x_155; uint16_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint32_t x_161; uint16_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; 
x_144 = l_List_reverse___rarg(x_18);
x_145 = l_Lean_Format_flatten___main___closed__1;
x_146 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_144, x_145);
x_147 = 0;
x_148 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_149 = 0;
x_150 = 0;
x_151 = 0;
x_152 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_152, sizeof(void*)*2, x_149);
lean_ctor_set_uint16(x_152, sizeof(void*)*2 + 4, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 7, x_151);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_153 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_105);
x_154 = lean_box(1);
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_158, sizeof(void*)*2, x_155);
lean_ctor_set_uint16(x_158, sizeof(void*)*2 + 4, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 7, x_157);
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = 0;
x_162 = 0;
x_163 = 0;
x_164 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_164, 0, x_152);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_164, sizeof(void*)*2, x_161);
lean_ctor_set_uint16(x_164, sizeof(void*)*2 + 4, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*2 + 7, x_163);
x_165 = lean_format_group(x_164);
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_169, 0, x_21);
lean_ctor_set(x_169, 1, x_165);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_169, sizeof(void*)*2, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*2 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 7, x_168);
lean_ctor_set(x_24, 1, x_169);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_105);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_22);
lean_ctor_set(x_171, 1, x_18);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_172);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_171);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_24, 0);
lean_inc(x_174);
lean_dec(x_24);
x_175 = lean_ctor_get(x_20, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_176 = x_20;
} else {
 lean_dec_ref(x_20);
 x_176 = lean_box(0);
}
x_177 = lean_expr_eqv(x_175, x_174);
if (x_177 == 0)
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = l_Lean_Format_isNil(x_21);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_22);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_176)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_176;
}
lean_ctor_set(x_181, 0, x_174);
if (x_178 == 0)
{
uint8_t x_182; lean_object* x_183; uint32_t x_184; uint16_t x_185; uint8_t x_186; lean_object* x_187; 
x_182 = 0;
x_183 = lean_box(1);
x_184 = 0;
x_185 = 0;
x_186 = 0;
x_187 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_187, 0, x_21);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set_uint8(x_187, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_187, sizeof(void*)*2, x_184);
lean_ctor_set_uint16(x_187, sizeof(void*)*2 + 4, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*2 + 7, x_186);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_188; 
lean_dec(x_175);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_15, 1, x_188);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint32_t x_194; uint16_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint32_t x_199; uint16_t x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint32_t x_205; uint16_t x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; uint32_t x_210; uint16_t x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_190 = l_List_reverse___rarg(x_18);
x_191 = l_Lean_Format_flatten___main___closed__1;
x_192 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_190, x_191);
x_193 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_194 = 0;
x_195 = 0;
x_196 = 0;
x_197 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_197, sizeof(void*)*2, x_194);
lean_ctor_set_uint16(x_197, sizeof(void*)*2 + 4, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 7, x_196);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_198 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_175);
x_199 = 0;
x_200 = 0;
x_201 = 0;
x_202 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_198);
lean_ctor_set_uint8(x_202, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_202, sizeof(void*)*2, x_199);
lean_ctor_set_uint16(x_202, sizeof(void*)*2 + 4, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*2 + 7, x_201);
x_203 = lean_unsigned_to_nat(2u);
x_204 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = 0;
x_206 = 0;
x_207 = 0;
x_208 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_208, 0, x_197);
lean_ctor_set(x_208, 1, x_204);
lean_ctor_set_uint8(x_208, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_208, sizeof(void*)*2, x_205);
lean_ctor_set_uint16(x_208, sizeof(void*)*2 + 4, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*2 + 7, x_207);
x_209 = lean_format_group(x_208);
x_210 = 0;
x_211 = 0;
x_212 = 0;
x_213 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_213, 0, x_187);
lean_ctor_set(x_213, 1, x_209);
lean_ctor_set_uint8(x_213, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_213, sizeof(void*)*2, x_210);
lean_ctor_set_uint16(x_213, sizeof(void*)*2 + 4, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*2 + 7, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_181);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_15, 1, x_214);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_216; 
lean_dec(x_175);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_181);
lean_ctor_set(x_216, 1, x_21);
lean_ctor_set(x_15, 1, x_216);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint32_t x_229; uint16_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint32_t x_235; uint16_t x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
x_218 = l_List_reverse___rarg(x_18);
x_219 = l_Lean_Format_flatten___main___closed__1;
x_220 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_218, x_219);
x_221 = 0;
x_222 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_223 = 0;
x_224 = 0;
x_225 = 0;
x_226 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_226, sizeof(void*)*2, x_223);
lean_ctor_set_uint16(x_226, sizeof(void*)*2 + 4, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 7, x_225);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_227 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_175);
x_228 = lean_box(1);
x_229 = 0;
x_230 = 0;
x_231 = 0;
x_232 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_227);
lean_ctor_set_uint8(x_232, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_232, sizeof(void*)*2, x_229);
lean_ctor_set_uint16(x_232, sizeof(void*)*2 + 4, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*2 + 7, x_231);
x_233 = lean_unsigned_to_nat(2u);
x_234 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = 0;
x_236 = 0;
x_237 = 0;
x_238 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_238, 0, x_226);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_238, sizeof(void*)*2, x_235);
lean_ctor_set_uint16(x_238, sizeof(void*)*2 + 4, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 7, x_237);
x_239 = lean_format_group(x_238);
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_243, 0, x_21);
lean_ctor_set(x_243, 1, x_239);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_243, sizeof(void*)*2, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*2 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 7, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_181);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_15, 1, x_244);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_175);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_22);
lean_ctor_set(x_246, 1, x_18);
if (lean_is_scalar(x_176)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_176;
}
lean_ctor_set(x_247, 0, x_174);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_21);
lean_ctor_set(x_15, 1, x_248);
lean_ctor_set(x_15, 0, x_246);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_15, 0);
x_251 = lean_ctor_get(x_15, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_15);
x_252 = lean_ctor_get(x_17, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_17, 3);
lean_inc(x_253);
lean_dec(x_17);
lean_inc(x_2);
x_254 = l_Lean_MetavarContext_instantiateMVars(x_2, x_253);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_18);
lean_ctor_set(x_11, 0, x_255);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_11);
lean_ctor_set(x_258, 1, x_251);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_7 = x_13;
x_8 = x_259;
goto _start;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_free_object(x_11);
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_262 = x_254;
} else {
 lean_dec_ref(x_254);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_250, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_264 = x_250;
} else {
 lean_dec_ref(x_250);
 x_264 = lean_box(0);
}
x_265 = lean_expr_eqv(x_263, x_261);
if (x_265 == 0)
{
uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = l_Lean_Format_isNil(x_251);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_252);
lean_ctor_set(x_268, 1, x_267);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_264;
}
lean_ctor_set(x_269, 0, x_261);
if (x_266 == 0)
{
uint8_t x_270; lean_object* x_271; uint32_t x_272; uint16_t x_273; uint8_t x_274; lean_object* x_275; 
x_270 = 0;
x_271 = lean_box(1);
x_272 = 0;
x_273 = 0;
x_274 = 0;
x_275 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_275, 0, x_251);
lean_ctor_set(x_275, 1, x_271);
lean_ctor_set_uint8(x_275, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_275, sizeof(void*)*2, x_272);
lean_ctor_set_uint16(x_275, sizeof(void*)*2 + 4, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*2 + 7, x_274);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_263);
if (lean_is_scalar(x_262)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_262;
}
lean_ctor_set(x_276, 0, x_269);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_268);
lean_ctor_set(x_277, 1, x_276);
x_7 = x_13;
x_8 = x_277;
goto _start;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint32_t x_283; uint16_t x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; uint32_t x_288; uint16_t x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint32_t x_294; uint16_t x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; uint32_t x_299; uint16_t x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_279 = l_List_reverse___rarg(x_18);
x_280 = l_Lean_Format_flatten___main___closed__1;
x_281 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_279, x_280);
x_282 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_283 = 0;
x_284 = 0;
x_285 = 0;
x_286 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_282);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_286, sizeof(void*)*2, x_283);
lean_ctor_set_uint16(x_286, sizeof(void*)*2 + 4, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 7, x_285);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_287 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_263);
x_288 = 0;
x_289 = 0;
x_290 = 0;
x_291 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_291, 0, x_271);
lean_ctor_set(x_291, 1, x_287);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_291, sizeof(void*)*2, x_288);
lean_ctor_set_uint16(x_291, sizeof(void*)*2 + 4, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 7, x_290);
x_292 = lean_unsigned_to_nat(2u);
x_293 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = 0;
x_295 = 0;
x_296 = 0;
x_297 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_293);
lean_ctor_set_uint8(x_297, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_297, sizeof(void*)*2, x_294);
lean_ctor_set_uint16(x_297, sizeof(void*)*2 + 4, x_295);
lean_ctor_set_uint8(x_297, sizeof(void*)*2 + 7, x_296);
x_298 = lean_format_group(x_297);
x_299 = 0;
x_300 = 0;
x_301 = 0;
x_302 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_302, 0, x_275);
lean_ctor_set(x_302, 1, x_298);
lean_ctor_set_uint8(x_302, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_302, sizeof(void*)*2, x_299);
lean_ctor_set_uint16(x_302, sizeof(void*)*2 + 4, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*2 + 7, x_301);
if (lean_is_scalar(x_262)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_262;
}
lean_ctor_set(x_303, 0, x_269);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_268);
lean_ctor_set(x_304, 1, x_303);
x_7 = x_13;
x_8 = x_304;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_263);
if (lean_is_scalar(x_262)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_262;
}
lean_ctor_set(x_306, 0, x_269);
lean_ctor_set(x_306, 1, x_251);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_268);
lean_ctor_set(x_307, 1, x_306);
x_7 = x_13;
x_8 = x_307;
goto _start;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint32_t x_314; uint16_t x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint32_t x_320; uint16_t x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint32_t x_326; uint16_t x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_309 = l_List_reverse___rarg(x_18);
x_310 = l_Lean_Format_flatten___main___closed__1;
x_311 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_309, x_310);
x_312 = 0;
x_313 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_314 = 0;
x_315 = 0;
x_316 = 0;
x_317 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_317, 0, x_311);
lean_ctor_set(x_317, 1, x_313);
lean_ctor_set_uint8(x_317, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_317, sizeof(void*)*2, x_314);
lean_ctor_set_uint16(x_317, sizeof(void*)*2 + 4, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*2 + 7, x_316);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_318 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_263);
x_319 = lean_box(1);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_318);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_323, sizeof(void*)*2, x_320);
lean_ctor_set_uint16(x_323, sizeof(void*)*2 + 4, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 7, x_322);
x_324 = lean_unsigned_to_nat(2u);
x_325 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = 0;
x_327 = 0;
x_328 = 0;
x_329 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_329, 0, x_317);
lean_ctor_set(x_329, 1, x_325);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_329, sizeof(void*)*2, x_326);
lean_ctor_set_uint16(x_329, sizeof(void*)*2 + 4, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 7, x_328);
x_330 = lean_format_group(x_329);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_334, 0, x_251);
lean_ctor_set(x_334, 1, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_334, sizeof(void*)*2, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*2 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 7, x_333);
if (lean_is_scalar(x_262)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_262;
}
lean_ctor_set(x_335, 0, x_269);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_268);
lean_ctor_set(x_336, 1, x_335);
x_7 = x_13;
x_8 = x_336;
goto _start;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_263);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_252);
lean_ctor_set(x_338, 1, x_18);
if (lean_is_scalar(x_264)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_264;
}
lean_ctor_set(x_339, 0, x_261);
if (lean_is_scalar(x_262)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_262;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_251);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
x_7 = x_13;
x_8 = x_341;
goto _start;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint32_t x_361; uint16_t x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; uint32_t x_366; uint16_t x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; uint32_t x_371; uint16_t x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_free_object(x_11);
x_343 = lean_ctor_get(x_8, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_344 = x_8;
} else {
 lean_dec_ref(x_8);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_15, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_15, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_347 = x_15;
} else {
 lean_dec_ref(x_15);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_17, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_17, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_17, 4);
lean_inc(x_350);
lean_dec(x_17);
x_351 = l_Lean_Format_isNil(x_346);
lean_inc(x_2);
x_352 = l_Lean_MetavarContext_instantiateMVars(x_2, x_349);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec(x_352);
lean_inc(x_2);
x_354 = l_Lean_MetavarContext_instantiateMVars(x_2, x_350);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
lean_dec(x_354);
x_356 = l_Lean_Name_toString___closed__1;
x_357 = l_Lean_Name_toStringWithSep___main(x_356, x_348);
x_358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_358, 0, x_357);
x_359 = 0;
x_360 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_361 = 0;
x_362 = 0;
x_363 = 0;
x_364 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_360);
lean_ctor_set_uint8(x_364, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_364, sizeof(void*)*2, x_361);
lean_ctor_set_uint16(x_364, sizeof(void*)*2 + 4, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*2 + 7, x_363);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_365 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_353);
x_366 = 0;
x_367 = 0;
x_368 = 0;
x_369 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_369, 0, x_364);
lean_ctor_set(x_369, 1, x_365);
lean_ctor_set_uint8(x_369, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_369, sizeof(void*)*2, x_366);
lean_ctor_set_uint16(x_369, sizeof(void*)*2 + 4, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*2 + 7, x_368);
x_370 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_371 = 0;
x_372 = 0;
x_373 = 0;
x_374 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_374, 0, x_369);
lean_ctor_set(x_374, 1, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_374, sizeof(void*)*2, x_371);
lean_ctor_set_uint16(x_374, sizeof(void*)*2 + 4, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*2 + 7, x_373);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_375 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_355);
x_376 = lean_box(1);
x_377 = 0;
x_378 = 0;
x_379 = 0;
x_380 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set(x_380, 1, x_375);
lean_ctor_set_uint8(x_380, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_380, sizeof(void*)*2, x_377);
lean_ctor_set_uint16(x_380, sizeof(void*)*2 + 4, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*2 + 7, x_379);
x_381 = lean_unsigned_to_nat(2u);
x_382 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_386, 0, x_374);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_386, sizeof(void*)*2, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*2 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*2 + 7, x_385);
x_387 = lean_format_group(x_386);
x_388 = lean_box(0);
x_389 = lean_box(0);
if (x_351 == 0)
{
uint32_t x_454; uint16_t x_455; uint8_t x_456; lean_object* x_457; 
x_454 = 0;
x_455 = 0;
x_456 = 0;
x_457 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_457, 0, x_346);
lean_ctor_set(x_457, 1, x_376);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_457, sizeof(void*)*2, x_454);
lean_ctor_set_uint16(x_457, sizeof(void*)*2 + 4, x_455);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 7, x_456);
if (lean_obj_tag(x_343) == 0)
{
uint8_t x_458; 
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
x_458 = l_Lean_Format_isNil(x_457);
if (x_458 == 0)
{
uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_462, 0, x_457);
lean_ctor_set(x_462, 1, x_376);
lean_ctor_set_uint8(x_462, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_462, sizeof(void*)*2, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*2 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*2 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
x_466 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_466, 0, x_462);
lean_ctor_set(x_466, 1, x_387);
lean_ctor_set_uint8(x_466, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_466, sizeof(void*)*2, x_463);
lean_ctor_set_uint16(x_466, sizeof(void*)*2 + 4, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*2 + 7, x_465);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_389);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_388);
lean_ctor_set(x_468, 1, x_467);
x_7 = x_13;
x_8 = x_468;
goto _start;
}
else
{
uint32_t x_470; uint16_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_470 = 0;
x_471 = 0;
x_472 = 0;
x_473 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_473, 0, x_457);
lean_ctor_set(x_473, 1, x_387);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_473, sizeof(void*)*2, x_470);
lean_ctor_set_uint16(x_473, sizeof(void*)*2 + 4, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 7, x_472);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_389);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_388);
lean_ctor_set(x_475, 1, x_474);
x_7 = x_13;
x_8 = x_475;
goto _start;
}
}
else
{
x_390 = x_457;
goto block_453;
}
}
else
{
if (lean_obj_tag(x_343) == 0)
{
uint32_t x_477; uint16_t x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
x_477 = 0;
x_478 = 0;
x_479 = 0;
x_480 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_480, 0, x_346);
lean_ctor_set(x_480, 1, x_387);
lean_ctor_set_uint8(x_480, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_480, sizeof(void*)*2, x_477);
lean_ctor_set_uint16(x_480, sizeof(void*)*2 + 4, x_478);
lean_ctor_set_uint8(x_480, sizeof(void*)*2 + 7, x_479);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_389);
lean_ctor_set(x_481, 1, x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_388);
lean_ctor_set(x_482, 1, x_481);
x_7 = x_13;
x_8 = x_482;
goto _start;
}
else
{
x_390 = x_346;
goto block_453;
}
}
block_453:
{
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_391; 
lean_dec(x_343);
x_391 = l_Lean_Format_isNil(x_390);
if (x_391 == 0)
{
uint32_t x_392; uint16_t x_393; uint8_t x_394; lean_object* x_395; uint32_t x_396; uint16_t x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_392 = 0;
x_393 = 0;
x_394 = 0;
x_395 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_395, 0, x_390);
lean_ctor_set(x_395, 1, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_395, sizeof(void*)*2, x_392);
lean_ctor_set_uint16(x_395, sizeof(void*)*2 + 4, x_393);
lean_ctor_set_uint8(x_395, sizeof(void*)*2 + 7, x_394);
x_396 = 0;
x_397 = 0;
x_398 = 0;
x_399 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_399, 0, x_395);
lean_ctor_set(x_399, 1, x_387);
lean_ctor_set_uint8(x_399, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_399, sizeof(void*)*2, x_396);
lean_ctor_set_uint16(x_399, sizeof(void*)*2 + 4, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*2 + 7, x_398);
if (lean_is_scalar(x_347)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_347;
}
lean_ctor_set(x_400, 0, x_389);
lean_ctor_set(x_400, 1, x_399);
if (lean_is_scalar(x_344)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_344;
}
lean_ctor_set(x_401, 0, x_388);
lean_ctor_set(x_401, 1, x_400);
x_7 = x_13;
x_8 = x_401;
goto _start;
}
else
{
uint32_t x_403; uint16_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_403 = 0;
x_404 = 0;
x_405 = 0;
x_406 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_406, 0, x_390);
lean_ctor_set(x_406, 1, x_387);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_406, sizeof(void*)*2, x_403);
lean_ctor_set_uint16(x_406, sizeof(void*)*2 + 4, x_404);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 7, x_405);
if (lean_is_scalar(x_347)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_347;
}
lean_ctor_set(x_407, 0, x_389);
lean_ctor_set(x_407, 1, x_406);
if (lean_is_scalar(x_344)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_344;
}
lean_ctor_set(x_408, 0, x_388);
lean_ctor_set(x_408, 1, x_407);
x_7 = x_13;
x_8 = x_408;
goto _start;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint32_t x_415; uint16_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; uint32_t x_420; uint16_t x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; uint32_t x_425; uint16_t x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; uint32_t x_430; uint16_t x_431; uint8_t x_432; lean_object* x_433; uint8_t x_434; 
x_410 = lean_ctor_get(x_345, 0);
lean_inc(x_410);
lean_dec(x_345);
x_411 = l_List_reverse___rarg(x_343);
x_412 = l_Lean_Format_flatten___main___closed__1;
x_413 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_411, x_412);
x_414 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_415 = 0;
x_416 = 0;
x_417 = 0;
x_418 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_418, 0, x_413);
lean_ctor_set(x_418, 1, x_414);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_418, sizeof(void*)*2, x_415);
lean_ctor_set_uint16(x_418, sizeof(void*)*2 + 4, x_416);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 7, x_417);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_419 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_410);
x_420 = 0;
x_421 = 0;
x_422 = 0;
x_423 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_423, 0, x_376);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_423, sizeof(void*)*2, x_420);
lean_ctor_set_uint16(x_423, sizeof(void*)*2 + 4, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 7, x_422);
x_424 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_424, 0, x_381);
lean_ctor_set(x_424, 1, x_423);
x_425 = 0;
x_426 = 0;
x_427 = 0;
x_428 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_428, sizeof(void*)*2, x_425);
lean_ctor_set_uint16(x_428, sizeof(void*)*2 + 4, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 7, x_427);
x_429 = lean_format_group(x_428);
x_430 = 0;
x_431 = 0;
x_432 = 0;
x_433 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_433, 0, x_390);
lean_ctor_set(x_433, 1, x_429);
lean_ctor_set_uint8(x_433, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_433, sizeof(void*)*2, x_430);
lean_ctor_set_uint16(x_433, sizeof(void*)*2 + 4, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*2 + 7, x_432);
x_434 = l_Lean_Format_isNil(x_433);
if (x_434 == 0)
{
uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_435 = 0;
x_436 = 0;
x_437 = 0;
x_438 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_438, 0, x_433);
lean_ctor_set(x_438, 1, x_376);
lean_ctor_set_uint8(x_438, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_438, sizeof(void*)*2, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*2 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*2 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_387);
lean_ctor_set_uint8(x_442, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_442, sizeof(void*)*2, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*2 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*2 + 7, x_441);
if (lean_is_scalar(x_347)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_347;
}
lean_ctor_set(x_443, 0, x_389);
lean_ctor_set(x_443, 1, x_442);
if (lean_is_scalar(x_344)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_344;
}
lean_ctor_set(x_444, 0, x_388);
lean_ctor_set(x_444, 1, x_443);
x_7 = x_13;
x_8 = x_444;
goto _start;
}
else
{
uint32_t x_446; uint16_t x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_446 = 0;
x_447 = 0;
x_448 = 0;
x_449 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_449, 0, x_433);
lean_ctor_set(x_449, 1, x_387);
lean_ctor_set_uint8(x_449, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_449, sizeof(void*)*2, x_446);
lean_ctor_set_uint16(x_449, sizeof(void*)*2 + 4, x_447);
lean_ctor_set_uint8(x_449, sizeof(void*)*2 + 7, x_448);
if (lean_is_scalar(x_347)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_347;
}
lean_ctor_set(x_450, 0, x_389);
lean_ctor_set(x_450, 1, x_449);
if (lean_is_scalar(x_344)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_344;
}
lean_ctor_set(x_451, 0, x_388);
lean_ctor_set(x_451, 1, x_450);
x_7 = x_13;
x_8 = x_451;
goto _start;
}
}
}
}
}
else
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_11, 0);
lean_inc(x_484);
lean_dec(x_11);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_485 = lean_ctor_get(x_8, 0);
lean_inc(x_485);
lean_dec(x_8);
x_486 = lean_ctor_get(x_15, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_15, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_488 = x_15;
} else {
 lean_dec_ref(x_15);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_484, 2);
lean_inc(x_489);
x_490 = lean_ctor_get(x_484, 3);
lean_inc(x_490);
lean_dec(x_484);
lean_inc(x_2);
x_491 = l_Lean_MetavarContext_instantiateMVars(x_2, x_490);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_485);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_492);
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_493;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_488;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_496);
x_7 = x_13;
x_8 = x_497;
goto _start;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_499 = lean_ctor_get(x_491, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_500 = x_491;
} else {
 lean_dec_ref(x_491);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_486, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_502 = x_486;
} else {
 lean_dec_ref(x_486);
 x_502 = lean_box(0);
}
x_503 = lean_expr_eqv(x_501, x_499);
if (x_503 == 0)
{
uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = l_Lean_Format_isNil(x_487);
x_505 = lean_box(0);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_489);
lean_ctor_set(x_506, 1, x_505);
if (lean_is_scalar(x_502)) {
 x_507 = lean_alloc_ctor(1, 1, 0);
} else {
 x_507 = x_502;
}
lean_ctor_set(x_507, 0, x_499);
if (x_504 == 0)
{
uint8_t x_508; lean_object* x_509; uint32_t x_510; uint16_t x_511; uint8_t x_512; lean_object* x_513; 
x_508 = 0;
x_509 = lean_box(1);
x_510 = 0;
x_511 = 0;
x_512 = 0;
x_513 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_513, 0, x_487);
lean_ctor_set(x_513, 1, x_509);
lean_ctor_set_uint8(x_513, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_513, sizeof(void*)*2, x_510);
lean_ctor_set_uint16(x_513, sizeof(void*)*2 + 4, x_511);
lean_ctor_set_uint8(x_513, sizeof(void*)*2 + 7, x_512);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_501);
if (lean_is_scalar(x_500)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_500;
}
lean_ctor_set(x_514, 0, x_507);
lean_ctor_set(x_514, 1, x_513);
if (lean_is_scalar(x_488)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_488;
}
lean_ctor_set(x_515, 0, x_506);
lean_ctor_set(x_515, 1, x_514);
x_7 = x_13;
x_8 = x_515;
goto _start;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint32_t x_521; uint16_t x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; uint32_t x_537; uint16_t x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_517 = l_List_reverse___rarg(x_485);
x_518 = l_Lean_Format_flatten___main___closed__1;
x_519 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_517, x_518);
x_520 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_521 = 0;
x_522 = 0;
x_523 = 0;
x_524 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_524, 0, x_519);
lean_ctor_set(x_524, 1, x_520);
lean_ctor_set_uint8(x_524, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_524, sizeof(void*)*2, x_521);
lean_ctor_set_uint16(x_524, sizeof(void*)*2 + 4, x_522);
lean_ctor_set_uint8(x_524, sizeof(void*)*2 + 7, x_523);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_525 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_501);
x_526 = 0;
x_527 = 0;
x_528 = 0;
x_529 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_529, 0, x_509);
lean_ctor_set(x_529, 1, x_525);
lean_ctor_set_uint8(x_529, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_529, sizeof(void*)*2, x_526);
lean_ctor_set_uint16(x_529, sizeof(void*)*2 + 4, x_527);
lean_ctor_set_uint8(x_529, sizeof(void*)*2 + 7, x_528);
x_530 = lean_unsigned_to_nat(2u);
x_531 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_529);
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_535, 0, x_524);
lean_ctor_set(x_535, 1, x_531);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_535, sizeof(void*)*2, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*2 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 7, x_534);
x_536 = lean_format_group(x_535);
x_537 = 0;
x_538 = 0;
x_539 = 0;
x_540 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_540, 0, x_513);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_540, sizeof(void*)*2, x_537);
lean_ctor_set_uint16(x_540, sizeof(void*)*2 + 4, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 7, x_539);
if (lean_is_scalar(x_500)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_500;
}
lean_ctor_set(x_541, 0, x_507);
lean_ctor_set(x_541, 1, x_540);
if (lean_is_scalar(x_488)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_488;
}
lean_ctor_set(x_542, 0, x_506);
lean_ctor_set(x_542, 1, x_541);
x_7 = x_13;
x_8 = x_542;
goto _start;
}
}
else
{
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_501);
if (lean_is_scalar(x_500)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_500;
}
lean_ctor_set(x_544, 0, x_507);
lean_ctor_set(x_544, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_488;
}
lean_ctor_set(x_545, 0, x_506);
lean_ctor_set(x_545, 1, x_544);
x_7 = x_13;
x_8 = x_545;
goto _start;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; uint32_t x_552; uint16_t x_553; uint8_t x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; lean_object* x_568; uint32_t x_569; uint16_t x_570; uint8_t x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_547 = l_List_reverse___rarg(x_485);
x_548 = l_Lean_Format_flatten___main___closed__1;
x_549 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_547, x_548);
x_550 = 0;
x_551 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_552 = 0;
x_553 = 0;
x_554 = 0;
x_555 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_555, 0, x_549);
lean_ctor_set(x_555, 1, x_551);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_555, sizeof(void*)*2, x_552);
lean_ctor_set_uint16(x_555, sizeof(void*)*2 + 4, x_553);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 7, x_554);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_556 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_501);
x_557 = lean_box(1);
x_558 = 0;
x_559 = 0;
x_560 = 0;
x_561 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_561, 0, x_557);
lean_ctor_set(x_561, 1, x_556);
lean_ctor_set_uint8(x_561, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_561, sizeof(void*)*2, x_558);
lean_ctor_set_uint16(x_561, sizeof(void*)*2 + 4, x_559);
lean_ctor_set_uint8(x_561, sizeof(void*)*2 + 7, x_560);
x_562 = lean_unsigned_to_nat(2u);
x_563 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_567, 0, x_555);
lean_ctor_set(x_567, 1, x_563);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_567, sizeof(void*)*2, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*2 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 7, x_566);
x_568 = lean_format_group(x_567);
x_569 = 0;
x_570 = 0;
x_571 = 0;
x_572 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_572, 0, x_487);
lean_ctor_set(x_572, 1, x_568);
lean_ctor_set_uint8(x_572, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_572, sizeof(void*)*2, x_569);
lean_ctor_set_uint16(x_572, sizeof(void*)*2 + 4, x_570);
lean_ctor_set_uint8(x_572, sizeof(void*)*2 + 7, x_571);
if (lean_is_scalar(x_500)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_500;
}
lean_ctor_set(x_573, 0, x_507);
lean_ctor_set(x_573, 1, x_572);
if (lean_is_scalar(x_488)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_488;
}
lean_ctor_set(x_574, 0, x_506);
lean_ctor_set(x_574, 1, x_573);
x_7 = x_13;
x_8 = x_574;
goto _start;
}
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_501);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_489);
lean_ctor_set(x_576, 1, x_485);
if (lean_is_scalar(x_502)) {
 x_577 = lean_alloc_ctor(1, 1, 0);
} else {
 x_577 = x_502;
}
lean_ctor_set(x_577, 0, x_499);
if (lean_is_scalar(x_500)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_500;
}
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_488;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_578);
x_7 = x_13;
x_8 = x_579;
goto _start;
}
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; lean_object* x_603; uint32_t x_604; uint16_t x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; uint32_t x_609; uint16_t x_610; uint8_t x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint32_t x_621; uint16_t x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_581 = lean_ctor_get(x_8, 0);
lean_inc(x_581);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_582 = x_8;
} else {
 lean_dec_ref(x_8);
 x_582 = lean_box(0);
}
x_583 = lean_ctor_get(x_15, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_15, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_585 = x_15;
} else {
 lean_dec_ref(x_15);
 x_585 = lean_box(0);
}
x_586 = lean_ctor_get(x_484, 2);
lean_inc(x_586);
x_587 = lean_ctor_get(x_484, 3);
lean_inc(x_587);
x_588 = lean_ctor_get(x_484, 4);
lean_inc(x_588);
lean_dec(x_484);
x_589 = l_Lean_Format_isNil(x_584);
lean_inc(x_2);
x_590 = l_Lean_MetavarContext_instantiateMVars(x_2, x_587);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec(x_590);
lean_inc(x_2);
x_592 = l_Lean_MetavarContext_instantiateMVars(x_2, x_588);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec(x_592);
x_594 = l_Lean_Name_toString___closed__1;
x_595 = l_Lean_Name_toStringWithSep___main(x_594, x_586);
x_596 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_596, 0, x_595);
x_597 = 0;
x_598 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_599 = 0;
x_600 = 0;
x_601 = 0;
x_602 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_598);
lean_ctor_set_uint8(x_602, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_602, sizeof(void*)*2, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*2 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*2 + 7, x_601);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_603 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_591);
x_604 = 0;
x_605 = 0;
x_606 = 0;
x_607 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_607, 0, x_602);
lean_ctor_set(x_607, 1, x_603);
lean_ctor_set_uint8(x_607, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_607, sizeof(void*)*2, x_604);
lean_ctor_set_uint16(x_607, sizeof(void*)*2 + 4, x_605);
lean_ctor_set_uint8(x_607, sizeof(void*)*2 + 7, x_606);
x_608 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_609 = 0;
x_610 = 0;
x_611 = 0;
x_612 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_612, 0, x_607);
lean_ctor_set(x_612, 1, x_608);
lean_ctor_set_uint8(x_612, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_612, sizeof(void*)*2, x_609);
lean_ctor_set_uint16(x_612, sizeof(void*)*2 + 4, x_610);
lean_ctor_set_uint8(x_612, sizeof(void*)*2 + 7, x_611);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_613 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_593);
x_614 = lean_box(1);
x_615 = 0;
x_616 = 0;
x_617 = 0;
x_618 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_618, 0, x_614);
lean_ctor_set(x_618, 1, x_613);
lean_ctor_set_uint8(x_618, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_618, sizeof(void*)*2, x_615);
lean_ctor_set_uint16(x_618, sizeof(void*)*2 + 4, x_616);
lean_ctor_set_uint8(x_618, sizeof(void*)*2 + 7, x_617);
x_619 = lean_unsigned_to_nat(2u);
x_620 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_618);
x_621 = 0;
x_622 = 0;
x_623 = 0;
x_624 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_624, 0, x_612);
lean_ctor_set(x_624, 1, x_620);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_624, sizeof(void*)*2, x_621);
lean_ctor_set_uint16(x_624, sizeof(void*)*2 + 4, x_622);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 7, x_623);
x_625 = lean_format_group(x_624);
x_626 = lean_box(0);
x_627 = lean_box(0);
if (x_589 == 0)
{
uint32_t x_692; uint16_t x_693; uint8_t x_694; lean_object* x_695; 
x_692 = 0;
x_693 = 0;
x_694 = 0;
x_695 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_695, 0, x_584);
lean_ctor_set(x_695, 1, x_614);
lean_ctor_set_uint8(x_695, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_695, sizeof(void*)*2, x_692);
lean_ctor_set_uint16(x_695, sizeof(void*)*2 + 4, x_693);
lean_ctor_set_uint8(x_695, sizeof(void*)*2 + 7, x_694);
if (lean_obj_tag(x_581) == 0)
{
uint8_t x_696; 
lean_dec(x_585);
lean_dec(x_583);
lean_dec(x_582);
x_696 = l_Lean_Format_isNil(x_695);
if (x_696 == 0)
{
uint32_t x_697; uint16_t x_698; uint8_t x_699; lean_object* x_700; uint32_t x_701; uint16_t x_702; uint8_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_697 = 0;
x_698 = 0;
x_699 = 0;
x_700 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_700, 0, x_695);
lean_ctor_set(x_700, 1, x_614);
lean_ctor_set_uint8(x_700, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_700, sizeof(void*)*2, x_697);
lean_ctor_set_uint16(x_700, sizeof(void*)*2 + 4, x_698);
lean_ctor_set_uint8(x_700, sizeof(void*)*2 + 7, x_699);
x_701 = 0;
x_702 = 0;
x_703 = 0;
x_704 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_704, 0, x_700);
lean_ctor_set(x_704, 1, x_625);
lean_ctor_set_uint8(x_704, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_704, sizeof(void*)*2, x_701);
lean_ctor_set_uint16(x_704, sizeof(void*)*2 + 4, x_702);
lean_ctor_set_uint8(x_704, sizeof(void*)*2 + 7, x_703);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_627);
lean_ctor_set(x_705, 1, x_704);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_626);
lean_ctor_set(x_706, 1, x_705);
x_7 = x_13;
x_8 = x_706;
goto _start;
}
else
{
uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_711, 0, x_695);
lean_ctor_set(x_711, 1, x_625);
lean_ctor_set_uint8(x_711, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_711, sizeof(void*)*2, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*2 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*2 + 7, x_710);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_627);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_626);
lean_ctor_set(x_713, 1, x_712);
x_7 = x_13;
x_8 = x_713;
goto _start;
}
}
else
{
x_628 = x_695;
goto block_691;
}
}
else
{
if (lean_obj_tag(x_581) == 0)
{
uint32_t x_715; uint16_t x_716; uint8_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_585);
lean_dec(x_583);
lean_dec(x_582);
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_718, 0, x_584);
lean_ctor_set(x_718, 1, x_625);
lean_ctor_set_uint8(x_718, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_718, sizeof(void*)*2, x_715);
lean_ctor_set_uint16(x_718, sizeof(void*)*2 + 4, x_716);
lean_ctor_set_uint8(x_718, sizeof(void*)*2 + 7, x_717);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_627);
lean_ctor_set(x_719, 1, x_718);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_626);
lean_ctor_set(x_720, 1, x_719);
x_7 = x_13;
x_8 = x_720;
goto _start;
}
else
{
x_628 = x_584;
goto block_691;
}
}
block_691:
{
if (lean_obj_tag(x_583) == 0)
{
uint8_t x_629; 
lean_dec(x_581);
x_629 = l_Lean_Format_isNil(x_628);
if (x_629 == 0)
{
uint32_t x_630; uint16_t x_631; uint8_t x_632; lean_object* x_633; uint32_t x_634; uint16_t x_635; uint8_t x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_630 = 0;
x_631 = 0;
x_632 = 0;
x_633 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_633, 0, x_628);
lean_ctor_set(x_633, 1, x_614);
lean_ctor_set_uint8(x_633, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_633, sizeof(void*)*2, x_630);
lean_ctor_set_uint16(x_633, sizeof(void*)*2 + 4, x_631);
lean_ctor_set_uint8(x_633, sizeof(void*)*2 + 7, x_632);
x_634 = 0;
x_635 = 0;
x_636 = 0;
x_637 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_637, 0, x_633);
lean_ctor_set(x_637, 1, x_625);
lean_ctor_set_uint8(x_637, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_637, sizeof(void*)*2, x_634);
lean_ctor_set_uint16(x_637, sizeof(void*)*2 + 4, x_635);
lean_ctor_set_uint8(x_637, sizeof(void*)*2 + 7, x_636);
if (lean_is_scalar(x_585)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_585;
}
lean_ctor_set(x_638, 0, x_627);
lean_ctor_set(x_638, 1, x_637);
if (lean_is_scalar(x_582)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_582;
}
lean_ctor_set(x_639, 0, x_626);
lean_ctor_set(x_639, 1, x_638);
x_7 = x_13;
x_8 = x_639;
goto _start;
}
else
{
uint32_t x_641; uint16_t x_642; uint8_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_641 = 0;
x_642 = 0;
x_643 = 0;
x_644 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_644, 0, x_628);
lean_ctor_set(x_644, 1, x_625);
lean_ctor_set_uint8(x_644, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_644, sizeof(void*)*2, x_641);
lean_ctor_set_uint16(x_644, sizeof(void*)*2 + 4, x_642);
lean_ctor_set_uint8(x_644, sizeof(void*)*2 + 7, x_643);
if (lean_is_scalar(x_585)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_585;
}
lean_ctor_set(x_645, 0, x_627);
lean_ctor_set(x_645, 1, x_644);
if (lean_is_scalar(x_582)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_582;
}
lean_ctor_set(x_646, 0, x_626);
lean_ctor_set(x_646, 1, x_645);
x_7 = x_13;
x_8 = x_646;
goto _start;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint32_t x_653; uint16_t x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; uint32_t x_658; uint16_t x_659; uint8_t x_660; lean_object* x_661; lean_object* x_662; uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; uint32_t x_668; uint16_t x_669; uint8_t x_670; lean_object* x_671; uint8_t x_672; 
x_648 = lean_ctor_get(x_583, 0);
lean_inc(x_648);
lean_dec(x_583);
x_649 = l_List_reverse___rarg(x_581);
x_650 = l_Lean_Format_flatten___main___closed__1;
x_651 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_649, x_650);
x_652 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_653 = 0;
x_654 = 0;
x_655 = 0;
x_656 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_656, 0, x_651);
lean_ctor_set(x_656, 1, x_652);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_656, sizeof(void*)*2, x_653);
lean_ctor_set_uint16(x_656, sizeof(void*)*2 + 4, x_654);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 7, x_655);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_657 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_648);
x_658 = 0;
x_659 = 0;
x_660 = 0;
x_661 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_661, 0, x_614);
lean_ctor_set(x_661, 1, x_657);
lean_ctor_set_uint8(x_661, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_661, sizeof(void*)*2, x_658);
lean_ctor_set_uint16(x_661, sizeof(void*)*2 + 4, x_659);
lean_ctor_set_uint8(x_661, sizeof(void*)*2 + 7, x_660);
x_662 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_662, 0, x_619);
lean_ctor_set(x_662, 1, x_661);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_666, 0, x_656);
lean_ctor_set(x_666, 1, x_662);
lean_ctor_set_uint8(x_666, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_666, sizeof(void*)*2, x_663);
lean_ctor_set_uint16(x_666, sizeof(void*)*2 + 4, x_664);
lean_ctor_set_uint8(x_666, sizeof(void*)*2 + 7, x_665);
x_667 = lean_format_group(x_666);
x_668 = 0;
x_669 = 0;
x_670 = 0;
x_671 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_671, 0, x_628);
lean_ctor_set(x_671, 1, x_667);
lean_ctor_set_uint8(x_671, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_671, sizeof(void*)*2, x_668);
lean_ctor_set_uint16(x_671, sizeof(void*)*2 + 4, x_669);
lean_ctor_set_uint8(x_671, sizeof(void*)*2 + 7, x_670);
x_672 = l_Lean_Format_isNil(x_671);
if (x_672 == 0)
{
uint32_t x_673; uint16_t x_674; uint8_t x_675; lean_object* x_676; uint32_t x_677; uint16_t x_678; uint8_t x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_673 = 0;
x_674 = 0;
x_675 = 0;
x_676 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_676, 0, x_671);
lean_ctor_set(x_676, 1, x_614);
lean_ctor_set_uint8(x_676, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_676, sizeof(void*)*2, x_673);
lean_ctor_set_uint16(x_676, sizeof(void*)*2 + 4, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*2 + 7, x_675);
x_677 = 0;
x_678 = 0;
x_679 = 0;
x_680 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_680, 0, x_676);
lean_ctor_set(x_680, 1, x_625);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_680, sizeof(void*)*2, x_677);
lean_ctor_set_uint16(x_680, sizeof(void*)*2 + 4, x_678);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 7, x_679);
if (lean_is_scalar(x_585)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_585;
}
lean_ctor_set(x_681, 0, x_627);
lean_ctor_set(x_681, 1, x_680);
if (lean_is_scalar(x_582)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_582;
}
lean_ctor_set(x_682, 0, x_626);
lean_ctor_set(x_682, 1, x_681);
x_7 = x_13;
x_8 = x_682;
goto _start;
}
else
{
uint32_t x_684; uint16_t x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_684 = 0;
x_685 = 0;
x_686 = 0;
x_687 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_687, 0, x_671);
lean_ctor_set(x_687, 1, x_625);
lean_ctor_set_uint8(x_687, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_687, sizeof(void*)*2, x_684);
lean_ctor_set_uint16(x_687, sizeof(void*)*2 + 4, x_685);
lean_ctor_set_uint8(x_687, sizeof(void*)*2 + 7, x_686);
if (lean_is_scalar(x_585)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_585;
}
lean_ctor_set(x_688, 0, x_627);
lean_ctor_set(x_688, 1, x_687);
if (lean_is_scalar(x_582)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_582;
}
lean_ctor_set(x_689, 0, x_626);
lean_ctor_set(x_689, 1, x_688);
x_7 = x_13;
x_8 = x_689;
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
uint8_t x_43; lean_object* x_44; uint32_t x_45; uint16_t x_46; uint8_t x_47; lean_object* x_48; 
x_43 = 0;
x_44 = lean_box(1);
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_48, 0, x_21);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_48, sizeof(void*)*2, x_45);
lean_ctor_set_uint16(x_48, sizeof(void*)*2 + 4, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*2 + 7, x_47);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_38);
lean_ctor_set(x_24, 1, x_48);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_42);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; uint16_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; uint32_t x_59; uint16_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint32_t x_65; uint16_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; lean_object* x_73; 
x_50 = l_List_reverse___rarg(x_18);
x_51 = l_Lean_Format_flatten___main___closed__1;
x_52 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_50, x_51);
x_53 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_54 = 0;
x_55 = 0;
x_56 = 0;
x_57 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_uint16(x_57, sizeof(void*)*2 + 4, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 7, x_56);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_59 = 0;
x_60 = 0;
x_61 = 0;
x_62 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_62, sizeof(void*)*2, x_59);
lean_ctor_set_uint16(x_62, sizeof(void*)*2 + 4, x_60);
lean_ctor_set_uint8(x_62, sizeof(void*)*2 + 7, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = 0;
x_66 = 0;
x_67 = 0;
x_68 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_68, sizeof(void*)*2, x_65);
lean_ctor_set_uint16(x_68, sizeof(void*)*2 + 4, x_66);
lean_ctor_set_uint8(x_68, sizeof(void*)*2 + 7, x_67);
x_69 = lean_format_group(x_68);
x_70 = 0;
x_71 = 0;
x_72 = 0;
x_73 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_73, 0, x_48);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 6, x_43);
lean_ctor_set_uint32(x_73, sizeof(void*)*2, x_70);
lean_ctor_set_uint16(x_73, sizeof(void*)*2 + 4, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 7, x_72);
lean_ctor_set(x_24, 1, x_73);
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
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; uint32_t x_81; uint16_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint32_t x_87; uint16_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint32_t x_93; uint16_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; uint32_t x_98; uint16_t x_99; uint8_t x_100; lean_object* x_101; 
x_76 = l_List_reverse___rarg(x_18);
x_77 = l_Lean_Format_flatten___main___closed__1;
x_78 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_76, x_77);
x_79 = 0;
x_80 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_81 = 0;
x_82 = 0;
x_83 = 0;
x_84 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_84, 0, x_78);
lean_ctor_set(x_84, 1, x_80);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_84, sizeof(void*)*2, x_81);
lean_ctor_set_uint16(x_84, sizeof(void*)*2 + 4, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 7, x_83);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_85 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_38);
x_86 = lean_box(1);
x_87 = 0;
x_88 = 0;
x_89 = 0;
x_90 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_90, sizeof(void*)*2, x_87);
lean_ctor_set_uint16(x_90, sizeof(void*)*2 + 4, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 7, x_89);
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = 0;
x_94 = 0;
x_95 = 0;
x_96 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_96, sizeof(void*)*2, x_93);
lean_ctor_set_uint16(x_96, sizeof(void*)*2 + 4, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*2 + 7, x_95);
x_97 = lean_format_group(x_96);
x_98 = 0;
x_99 = 0;
x_100 = 0;
x_101 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_101, 0, x_21);
lean_ctor_set(x_101, 1, x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 6, x_79);
lean_ctor_set_uint32(x_101, sizeof(void*)*2, x_98);
lean_ctor_set_uint16(x_101, sizeof(void*)*2 + 4, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 7, x_100);
lean_ctor_set(x_24, 1, x_101);
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
lean_object* x_103; 
lean_dec(x_38);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_22);
lean_ctor_set(x_103, 1, x_18);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_103);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_20, 0);
lean_inc(x_105);
lean_dec(x_20);
x_106 = lean_expr_eqv(x_105, x_35);
if (x_106 == 0)
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = l_Lean_Format_isNil(x_21);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_22);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_35);
if (x_107 == 0)
{
uint8_t x_111; lean_object* x_112; uint32_t x_113; uint16_t x_114; uint8_t x_115; lean_object* x_116; 
x_111 = 0;
x_112 = lean_box(1);
x_113 = 0;
x_114 = 0;
x_115 = 0;
x_116 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_116, 0, x_21);
lean_ctor_set(x_116, 1, x_112);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_116, sizeof(void*)*2, x_113);
lean_ctor_set_uint16(x_116, sizeof(void*)*2 + 4, x_114);
lean_ctor_set_uint8(x_116, sizeof(void*)*2 + 7, x_115);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_105);
lean_ctor_set(x_24, 1, x_116);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint32_t x_122; uint16_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint32_t x_127; uint16_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint32_t x_133; uint16_t x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; uint32_t x_138; uint16_t x_139; uint8_t x_140; lean_object* x_141; 
x_118 = l_List_reverse___rarg(x_18);
x_119 = l_Lean_Format_flatten___main___closed__1;
x_120 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_118, x_119);
x_121 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_122 = 0;
x_123 = 0;
x_124 = 0;
x_125 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_125, 0, x_120);
lean_ctor_set(x_125, 1, x_121);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_125, sizeof(void*)*2, x_122);
lean_ctor_set_uint16(x_125, sizeof(void*)*2 + 4, x_123);
lean_ctor_set_uint8(x_125, sizeof(void*)*2 + 7, x_124);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_126 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_105);
x_127 = 0;
x_128 = 0;
x_129 = 0;
x_130 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_130, 0, x_112);
lean_ctor_set(x_130, 1, x_126);
lean_ctor_set_uint8(x_130, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_130, sizeof(void*)*2, x_127);
lean_ctor_set_uint16(x_130, sizeof(void*)*2 + 4, x_128);
lean_ctor_set_uint8(x_130, sizeof(void*)*2 + 7, x_129);
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = 0;
x_134 = 0;
x_135 = 0;
x_136 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_136, sizeof(void*)*2, x_133);
lean_ctor_set_uint16(x_136, sizeof(void*)*2 + 4, x_134);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 7, x_135);
x_137 = lean_format_group(x_136);
x_138 = 0;
x_139 = 0;
x_140 = 0;
x_141 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_141, 0, x_116);
lean_ctor_set(x_141, 1, x_137);
lean_ctor_set_uint8(x_141, sizeof(void*)*2 + 6, x_111);
lean_ctor_set_uint32(x_141, sizeof(void*)*2, x_138);
lean_ctor_set_uint16(x_141, sizeof(void*)*2 + 4, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*2 + 7, x_140);
lean_ctor_set(x_24, 1, x_141);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_105);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; uint32_t x_149; uint16_t x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint32_t x_155; uint16_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint32_t x_161; uint16_t x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; uint32_t x_166; uint16_t x_167; uint8_t x_168; lean_object* x_169; 
x_144 = l_List_reverse___rarg(x_18);
x_145 = l_Lean_Format_flatten___main___closed__1;
x_146 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_144, x_145);
x_147 = 0;
x_148 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_149 = 0;
x_150 = 0;
x_151 = 0;
x_152 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_152, 0, x_146);
lean_ctor_set(x_152, 1, x_148);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_152, sizeof(void*)*2, x_149);
lean_ctor_set_uint16(x_152, sizeof(void*)*2 + 4, x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*2 + 7, x_151);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_153 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_105);
x_154 = lean_box(1);
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_153);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_158, sizeof(void*)*2, x_155);
lean_ctor_set_uint16(x_158, sizeof(void*)*2 + 4, x_156);
lean_ctor_set_uint8(x_158, sizeof(void*)*2 + 7, x_157);
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = 0;
x_162 = 0;
x_163 = 0;
x_164 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_164, 0, x_152);
lean_ctor_set(x_164, 1, x_160);
lean_ctor_set_uint8(x_164, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_164, sizeof(void*)*2, x_161);
lean_ctor_set_uint16(x_164, sizeof(void*)*2 + 4, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*2 + 7, x_163);
x_165 = lean_format_group(x_164);
x_166 = 0;
x_167 = 0;
x_168 = 0;
x_169 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_169, 0, x_21);
lean_ctor_set(x_169, 1, x_165);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 6, x_147);
lean_ctor_set_uint32(x_169, sizeof(void*)*2, x_166);
lean_ctor_set_uint16(x_169, sizeof(void*)*2 + 4, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 7, x_168);
lean_ctor_set(x_24, 1, x_169);
lean_ctor_set(x_24, 0, x_110);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_109);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_105);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_22);
lean_ctor_set(x_171, 1, x_18);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_35);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_172);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_171);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_24, 0);
lean_inc(x_174);
lean_dec(x_24);
x_175 = lean_ctor_get(x_20, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_176 = x_20;
} else {
 lean_dec_ref(x_20);
 x_176 = lean_box(0);
}
x_177 = lean_expr_eqv(x_175, x_174);
if (x_177 == 0)
{
uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = l_Lean_Format_isNil(x_21);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_22);
lean_ctor_set(x_180, 1, x_179);
if (lean_is_scalar(x_176)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_176;
}
lean_ctor_set(x_181, 0, x_174);
if (x_178 == 0)
{
uint8_t x_182; lean_object* x_183; uint32_t x_184; uint16_t x_185; uint8_t x_186; lean_object* x_187; 
x_182 = 0;
x_183 = lean_box(1);
x_184 = 0;
x_185 = 0;
x_186 = 0;
x_187 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_187, 0, x_21);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set_uint8(x_187, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_187, sizeof(void*)*2, x_184);
lean_ctor_set_uint16(x_187, sizeof(void*)*2 + 4, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*2 + 7, x_186);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_188; 
lean_dec(x_175);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_187);
lean_ctor_set(x_15, 1, x_188);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint32_t x_194; uint16_t x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; uint32_t x_199; uint16_t x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint32_t x_205; uint16_t x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; uint32_t x_210; uint16_t x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
x_190 = l_List_reverse___rarg(x_18);
x_191 = l_Lean_Format_flatten___main___closed__1;
x_192 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_190, x_191);
x_193 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_194 = 0;
x_195 = 0;
x_196 = 0;
x_197 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_197, 0, x_192);
lean_ctor_set(x_197, 1, x_193);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_197, sizeof(void*)*2, x_194);
lean_ctor_set_uint16(x_197, sizeof(void*)*2 + 4, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*2 + 7, x_196);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_198 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_175);
x_199 = 0;
x_200 = 0;
x_201 = 0;
x_202 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_198);
lean_ctor_set_uint8(x_202, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_202, sizeof(void*)*2, x_199);
lean_ctor_set_uint16(x_202, sizeof(void*)*2 + 4, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*2 + 7, x_201);
x_203 = lean_unsigned_to_nat(2u);
x_204 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = 0;
x_206 = 0;
x_207 = 0;
x_208 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_208, 0, x_197);
lean_ctor_set(x_208, 1, x_204);
lean_ctor_set_uint8(x_208, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_208, sizeof(void*)*2, x_205);
lean_ctor_set_uint16(x_208, sizeof(void*)*2 + 4, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*2 + 7, x_207);
x_209 = lean_format_group(x_208);
x_210 = 0;
x_211 = 0;
x_212 = 0;
x_213 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_213, 0, x_187);
lean_ctor_set(x_213, 1, x_209);
lean_ctor_set_uint8(x_213, sizeof(void*)*2 + 6, x_182);
lean_ctor_set_uint32(x_213, sizeof(void*)*2, x_210);
lean_ctor_set_uint16(x_213, sizeof(void*)*2 + 4, x_211);
lean_ctor_set_uint8(x_213, sizeof(void*)*2 + 7, x_212);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_181);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_15, 1, x_214);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_216; 
lean_dec(x_175);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_181);
lean_ctor_set(x_216, 1, x_21);
lean_ctor_set(x_15, 1, x_216);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint32_t x_223; uint16_t x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint32_t x_229; uint16_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint32_t x_235; uint16_t x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; uint32_t x_240; uint16_t x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
x_218 = l_List_reverse___rarg(x_18);
x_219 = l_Lean_Format_flatten___main___closed__1;
x_220 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_218, x_219);
x_221 = 0;
x_222 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_223 = 0;
x_224 = 0;
x_225 = 0;
x_226 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_226, 0, x_220);
lean_ctor_set(x_226, 1, x_222);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_226, sizeof(void*)*2, x_223);
lean_ctor_set_uint16(x_226, sizeof(void*)*2 + 4, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*2 + 7, x_225);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_227 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_175);
x_228 = lean_box(1);
x_229 = 0;
x_230 = 0;
x_231 = 0;
x_232 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_227);
lean_ctor_set_uint8(x_232, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_232, sizeof(void*)*2, x_229);
lean_ctor_set_uint16(x_232, sizeof(void*)*2 + 4, x_230);
lean_ctor_set_uint8(x_232, sizeof(void*)*2 + 7, x_231);
x_233 = lean_unsigned_to_nat(2u);
x_234 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = 0;
x_236 = 0;
x_237 = 0;
x_238 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_238, 0, x_226);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_238, sizeof(void*)*2, x_235);
lean_ctor_set_uint16(x_238, sizeof(void*)*2 + 4, x_236);
lean_ctor_set_uint8(x_238, sizeof(void*)*2 + 7, x_237);
x_239 = lean_format_group(x_238);
x_240 = 0;
x_241 = 0;
x_242 = 0;
x_243 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_243, 0, x_21);
lean_ctor_set(x_243, 1, x_239);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 6, x_221);
lean_ctor_set_uint32(x_243, sizeof(void*)*2, x_240);
lean_ctor_set_uint16(x_243, sizeof(void*)*2 + 4, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*2 + 7, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_181);
lean_ctor_set(x_244, 1, x_243);
lean_ctor_set(x_15, 1, x_244);
lean_ctor_set(x_15, 0, x_180);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_175);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_22);
lean_ctor_set(x_246, 1, x_18);
if (lean_is_scalar(x_176)) {
 x_247 = lean_alloc_ctor(1, 1, 0);
} else {
 x_247 = x_176;
}
lean_ctor_set(x_247, 0, x_174);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_21);
lean_ctor_set(x_15, 1, x_248);
lean_ctor_set(x_15, 0, x_246);
x_7 = x_13;
x_8 = x_15;
goto _start;
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_15, 0);
x_251 = lean_ctor_get(x_15, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_15);
x_252 = lean_ctor_get(x_17, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_17, 3);
lean_inc(x_253);
lean_dec(x_17);
lean_inc(x_2);
x_254 = l_Lean_MetavarContext_instantiateMVars(x_2, x_253);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_252);
lean_ctor_set(x_257, 1, x_18);
lean_ctor_set(x_11, 0, x_255);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_11);
lean_ctor_set(x_258, 1, x_251);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
x_7 = x_13;
x_8 = x_259;
goto _start;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_free_object(x_11);
x_261 = lean_ctor_get(x_254, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_262 = x_254;
} else {
 lean_dec_ref(x_254);
 x_262 = lean_box(0);
}
x_263 = lean_ctor_get(x_250, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_264 = x_250;
} else {
 lean_dec_ref(x_250);
 x_264 = lean_box(0);
}
x_265 = lean_expr_eqv(x_263, x_261);
if (x_265 == 0)
{
uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = l_Lean_Format_isNil(x_251);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_252);
lean_ctor_set(x_268, 1, x_267);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_264;
}
lean_ctor_set(x_269, 0, x_261);
if (x_266 == 0)
{
uint8_t x_270; lean_object* x_271; uint32_t x_272; uint16_t x_273; uint8_t x_274; lean_object* x_275; 
x_270 = 0;
x_271 = lean_box(1);
x_272 = 0;
x_273 = 0;
x_274 = 0;
x_275 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_275, 0, x_251);
lean_ctor_set(x_275, 1, x_271);
lean_ctor_set_uint8(x_275, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_275, sizeof(void*)*2, x_272);
lean_ctor_set_uint16(x_275, sizeof(void*)*2 + 4, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*2 + 7, x_274);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_263);
if (lean_is_scalar(x_262)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_262;
}
lean_ctor_set(x_276, 0, x_269);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_268);
lean_ctor_set(x_277, 1, x_276);
x_7 = x_13;
x_8 = x_277;
goto _start;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint32_t x_283; uint16_t x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; uint32_t x_288; uint16_t x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint32_t x_294; uint16_t x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; uint32_t x_299; uint16_t x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_279 = l_List_reverse___rarg(x_18);
x_280 = l_Lean_Format_flatten___main___closed__1;
x_281 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_279, x_280);
x_282 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_283 = 0;
x_284 = 0;
x_285 = 0;
x_286 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_282);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_286, sizeof(void*)*2, x_283);
lean_ctor_set_uint16(x_286, sizeof(void*)*2 + 4, x_284);
lean_ctor_set_uint8(x_286, sizeof(void*)*2 + 7, x_285);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_287 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_263);
x_288 = 0;
x_289 = 0;
x_290 = 0;
x_291 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_291, 0, x_271);
lean_ctor_set(x_291, 1, x_287);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_291, sizeof(void*)*2, x_288);
lean_ctor_set_uint16(x_291, sizeof(void*)*2 + 4, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*2 + 7, x_290);
x_292 = lean_unsigned_to_nat(2u);
x_293 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = 0;
x_295 = 0;
x_296 = 0;
x_297 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_293);
lean_ctor_set_uint8(x_297, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_297, sizeof(void*)*2, x_294);
lean_ctor_set_uint16(x_297, sizeof(void*)*2 + 4, x_295);
lean_ctor_set_uint8(x_297, sizeof(void*)*2 + 7, x_296);
x_298 = lean_format_group(x_297);
x_299 = 0;
x_300 = 0;
x_301 = 0;
x_302 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_302, 0, x_275);
lean_ctor_set(x_302, 1, x_298);
lean_ctor_set_uint8(x_302, sizeof(void*)*2 + 6, x_270);
lean_ctor_set_uint32(x_302, sizeof(void*)*2, x_299);
lean_ctor_set_uint16(x_302, sizeof(void*)*2 + 4, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*2 + 7, x_301);
if (lean_is_scalar(x_262)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_262;
}
lean_ctor_set(x_303, 0, x_269);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_268);
lean_ctor_set(x_304, 1, x_303);
x_7 = x_13;
x_8 = x_304;
goto _start;
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_306; lean_object* x_307; 
lean_dec(x_263);
if (lean_is_scalar(x_262)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_262;
}
lean_ctor_set(x_306, 0, x_269);
lean_ctor_set(x_306, 1, x_251);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_268);
lean_ctor_set(x_307, 1, x_306);
x_7 = x_13;
x_8 = x_307;
goto _start;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; uint32_t x_314; uint16_t x_315; uint8_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint32_t x_320; uint16_t x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint32_t x_326; uint16_t x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; uint32_t x_331; uint16_t x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_309 = l_List_reverse___rarg(x_18);
x_310 = l_Lean_Format_flatten___main___closed__1;
x_311 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_309, x_310);
x_312 = 0;
x_313 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_314 = 0;
x_315 = 0;
x_316 = 0;
x_317 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_317, 0, x_311);
lean_ctor_set(x_317, 1, x_313);
lean_ctor_set_uint8(x_317, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_317, sizeof(void*)*2, x_314);
lean_ctor_set_uint16(x_317, sizeof(void*)*2 + 4, x_315);
lean_ctor_set_uint8(x_317, sizeof(void*)*2 + 7, x_316);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_318 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_263);
x_319 = lean_box(1);
x_320 = 0;
x_321 = 0;
x_322 = 0;
x_323 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_323, 0, x_319);
lean_ctor_set(x_323, 1, x_318);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_323, sizeof(void*)*2, x_320);
lean_ctor_set_uint16(x_323, sizeof(void*)*2 + 4, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*2 + 7, x_322);
x_324 = lean_unsigned_to_nat(2u);
x_325 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_323);
x_326 = 0;
x_327 = 0;
x_328 = 0;
x_329 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_329, 0, x_317);
lean_ctor_set(x_329, 1, x_325);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_329, sizeof(void*)*2, x_326);
lean_ctor_set_uint16(x_329, sizeof(void*)*2 + 4, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 7, x_328);
x_330 = lean_format_group(x_329);
x_331 = 0;
x_332 = 0;
x_333 = 0;
x_334 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_334, 0, x_251);
lean_ctor_set(x_334, 1, x_330);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 6, x_312);
lean_ctor_set_uint32(x_334, sizeof(void*)*2, x_331);
lean_ctor_set_uint16(x_334, sizeof(void*)*2 + 4, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 7, x_333);
if (lean_is_scalar(x_262)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_262;
}
lean_ctor_set(x_335, 0, x_269);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_268);
lean_ctor_set(x_336, 1, x_335);
x_7 = x_13;
x_8 = x_336;
goto _start;
}
}
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_263);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_252);
lean_ctor_set(x_338, 1, x_18);
if (lean_is_scalar(x_264)) {
 x_339 = lean_alloc_ctor(1, 1, 0);
} else {
 x_339 = x_264;
}
lean_ctor_set(x_339, 0, x_261);
if (lean_is_scalar(x_262)) {
 x_340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_340 = x_262;
}
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_251);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_340);
x_7 = x_13;
x_8 = x_341;
goto _start;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; uint32_t x_361; uint16_t x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; uint32_t x_366; uint16_t x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; uint32_t x_371; uint16_t x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint32_t x_377; uint16_t x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint32_t x_383; uint16_t x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_free_object(x_11);
x_343 = lean_ctor_get(x_8, 0);
lean_inc(x_343);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_344 = x_8;
} else {
 lean_dec_ref(x_8);
 x_344 = lean_box(0);
}
x_345 = lean_ctor_get(x_15, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_15, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_347 = x_15;
} else {
 lean_dec_ref(x_15);
 x_347 = lean_box(0);
}
x_348 = lean_ctor_get(x_17, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_17, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_17, 4);
lean_inc(x_350);
lean_dec(x_17);
x_351 = l_Lean_Format_isNil(x_346);
lean_inc(x_2);
x_352 = l_Lean_MetavarContext_instantiateMVars(x_2, x_349);
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec(x_352);
lean_inc(x_2);
x_354 = l_Lean_MetavarContext_instantiateMVars(x_2, x_350);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
lean_dec(x_354);
x_356 = l_Lean_Name_toString___closed__1;
x_357 = l_Lean_Name_toStringWithSep___main(x_356, x_348);
x_358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_358, 0, x_357);
x_359 = 0;
x_360 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_361 = 0;
x_362 = 0;
x_363 = 0;
x_364 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_364, 0, x_358);
lean_ctor_set(x_364, 1, x_360);
lean_ctor_set_uint8(x_364, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_364, sizeof(void*)*2, x_361);
lean_ctor_set_uint16(x_364, sizeof(void*)*2 + 4, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*2 + 7, x_363);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_365 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_353);
x_366 = 0;
x_367 = 0;
x_368 = 0;
x_369 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_369, 0, x_364);
lean_ctor_set(x_369, 1, x_365);
lean_ctor_set_uint8(x_369, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_369, sizeof(void*)*2, x_366);
lean_ctor_set_uint16(x_369, sizeof(void*)*2 + 4, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*2 + 7, x_368);
x_370 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_371 = 0;
x_372 = 0;
x_373 = 0;
x_374 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_374, 0, x_369);
lean_ctor_set(x_374, 1, x_370);
lean_ctor_set_uint8(x_374, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_374, sizeof(void*)*2, x_371);
lean_ctor_set_uint16(x_374, sizeof(void*)*2 + 4, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*2 + 7, x_373);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_375 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_355);
x_376 = lean_box(1);
x_377 = 0;
x_378 = 0;
x_379 = 0;
x_380 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_380, 0, x_376);
lean_ctor_set(x_380, 1, x_375);
lean_ctor_set_uint8(x_380, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_380, sizeof(void*)*2, x_377);
lean_ctor_set_uint16(x_380, sizeof(void*)*2 + 4, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*2 + 7, x_379);
x_381 = lean_unsigned_to_nat(2u);
x_382 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_380);
x_383 = 0;
x_384 = 0;
x_385 = 0;
x_386 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_386, 0, x_374);
lean_ctor_set(x_386, 1, x_382);
lean_ctor_set_uint8(x_386, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_386, sizeof(void*)*2, x_383);
lean_ctor_set_uint16(x_386, sizeof(void*)*2 + 4, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*2 + 7, x_385);
x_387 = lean_format_group(x_386);
x_388 = lean_box(0);
x_389 = lean_box(0);
if (x_351 == 0)
{
uint32_t x_454; uint16_t x_455; uint8_t x_456; lean_object* x_457; 
x_454 = 0;
x_455 = 0;
x_456 = 0;
x_457 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_457, 0, x_346);
lean_ctor_set(x_457, 1, x_376);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_457, sizeof(void*)*2, x_454);
lean_ctor_set_uint16(x_457, sizeof(void*)*2 + 4, x_455);
lean_ctor_set_uint8(x_457, sizeof(void*)*2 + 7, x_456);
if (lean_obj_tag(x_343) == 0)
{
uint8_t x_458; 
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
x_458 = l_Lean_Format_isNil(x_457);
if (x_458 == 0)
{
uint32_t x_459; uint16_t x_460; uint8_t x_461; lean_object* x_462; uint32_t x_463; uint16_t x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_459 = 0;
x_460 = 0;
x_461 = 0;
x_462 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_462, 0, x_457);
lean_ctor_set(x_462, 1, x_376);
lean_ctor_set_uint8(x_462, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_462, sizeof(void*)*2, x_459);
lean_ctor_set_uint16(x_462, sizeof(void*)*2 + 4, x_460);
lean_ctor_set_uint8(x_462, sizeof(void*)*2 + 7, x_461);
x_463 = 0;
x_464 = 0;
x_465 = 0;
x_466 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_466, 0, x_462);
lean_ctor_set(x_466, 1, x_387);
lean_ctor_set_uint8(x_466, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_466, sizeof(void*)*2, x_463);
lean_ctor_set_uint16(x_466, sizeof(void*)*2 + 4, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*2 + 7, x_465);
x_467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_467, 0, x_389);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_388);
lean_ctor_set(x_468, 1, x_467);
x_7 = x_13;
x_8 = x_468;
goto _start;
}
else
{
uint32_t x_470; uint16_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_470 = 0;
x_471 = 0;
x_472 = 0;
x_473 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_473, 0, x_457);
lean_ctor_set(x_473, 1, x_387);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_473, sizeof(void*)*2, x_470);
lean_ctor_set_uint16(x_473, sizeof(void*)*2 + 4, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 7, x_472);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_389);
lean_ctor_set(x_474, 1, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_388);
lean_ctor_set(x_475, 1, x_474);
x_7 = x_13;
x_8 = x_475;
goto _start;
}
}
else
{
x_390 = x_457;
goto block_453;
}
}
else
{
if (lean_obj_tag(x_343) == 0)
{
uint32_t x_477; uint16_t x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_347);
lean_dec(x_345);
lean_dec(x_344);
x_477 = 0;
x_478 = 0;
x_479 = 0;
x_480 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_480, 0, x_346);
lean_ctor_set(x_480, 1, x_387);
lean_ctor_set_uint8(x_480, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_480, sizeof(void*)*2, x_477);
lean_ctor_set_uint16(x_480, sizeof(void*)*2 + 4, x_478);
lean_ctor_set_uint8(x_480, sizeof(void*)*2 + 7, x_479);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_389);
lean_ctor_set(x_481, 1, x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_388);
lean_ctor_set(x_482, 1, x_481);
x_7 = x_13;
x_8 = x_482;
goto _start;
}
else
{
x_390 = x_346;
goto block_453;
}
}
block_453:
{
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_391; 
lean_dec(x_343);
x_391 = l_Lean_Format_isNil(x_390);
if (x_391 == 0)
{
uint32_t x_392; uint16_t x_393; uint8_t x_394; lean_object* x_395; uint32_t x_396; uint16_t x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_392 = 0;
x_393 = 0;
x_394 = 0;
x_395 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_395, 0, x_390);
lean_ctor_set(x_395, 1, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_395, sizeof(void*)*2, x_392);
lean_ctor_set_uint16(x_395, sizeof(void*)*2 + 4, x_393);
lean_ctor_set_uint8(x_395, sizeof(void*)*2 + 7, x_394);
x_396 = 0;
x_397 = 0;
x_398 = 0;
x_399 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_399, 0, x_395);
lean_ctor_set(x_399, 1, x_387);
lean_ctor_set_uint8(x_399, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_399, sizeof(void*)*2, x_396);
lean_ctor_set_uint16(x_399, sizeof(void*)*2 + 4, x_397);
lean_ctor_set_uint8(x_399, sizeof(void*)*2 + 7, x_398);
if (lean_is_scalar(x_347)) {
 x_400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_400 = x_347;
}
lean_ctor_set(x_400, 0, x_389);
lean_ctor_set(x_400, 1, x_399);
if (lean_is_scalar(x_344)) {
 x_401 = lean_alloc_ctor(0, 2, 0);
} else {
 x_401 = x_344;
}
lean_ctor_set(x_401, 0, x_388);
lean_ctor_set(x_401, 1, x_400);
x_7 = x_13;
x_8 = x_401;
goto _start;
}
else
{
uint32_t x_403; uint16_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_403 = 0;
x_404 = 0;
x_405 = 0;
x_406 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_406, 0, x_390);
lean_ctor_set(x_406, 1, x_387);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_406, sizeof(void*)*2, x_403);
lean_ctor_set_uint16(x_406, sizeof(void*)*2 + 4, x_404);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 7, x_405);
if (lean_is_scalar(x_347)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_347;
}
lean_ctor_set(x_407, 0, x_389);
lean_ctor_set(x_407, 1, x_406);
if (lean_is_scalar(x_344)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_344;
}
lean_ctor_set(x_408, 0, x_388);
lean_ctor_set(x_408, 1, x_407);
x_7 = x_13;
x_8 = x_408;
goto _start;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint32_t x_415; uint16_t x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; uint32_t x_420; uint16_t x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; uint32_t x_425; uint16_t x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; uint32_t x_430; uint16_t x_431; uint8_t x_432; lean_object* x_433; uint8_t x_434; 
x_410 = lean_ctor_get(x_345, 0);
lean_inc(x_410);
lean_dec(x_345);
x_411 = l_List_reverse___rarg(x_343);
x_412 = l_Lean_Format_flatten___main___closed__1;
x_413 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_411, x_412);
x_414 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_415 = 0;
x_416 = 0;
x_417 = 0;
x_418 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_418, 0, x_413);
lean_ctor_set(x_418, 1, x_414);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_418, sizeof(void*)*2, x_415);
lean_ctor_set_uint16(x_418, sizeof(void*)*2 + 4, x_416);
lean_ctor_set_uint8(x_418, sizeof(void*)*2 + 7, x_417);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_419 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_410);
x_420 = 0;
x_421 = 0;
x_422 = 0;
x_423 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_423, 0, x_376);
lean_ctor_set(x_423, 1, x_419);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_423, sizeof(void*)*2, x_420);
lean_ctor_set_uint16(x_423, sizeof(void*)*2 + 4, x_421);
lean_ctor_set_uint8(x_423, sizeof(void*)*2 + 7, x_422);
x_424 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_424, 0, x_381);
lean_ctor_set(x_424, 1, x_423);
x_425 = 0;
x_426 = 0;
x_427 = 0;
x_428 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_428, 0, x_418);
lean_ctor_set(x_428, 1, x_424);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_428, sizeof(void*)*2, x_425);
lean_ctor_set_uint16(x_428, sizeof(void*)*2 + 4, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 7, x_427);
x_429 = lean_format_group(x_428);
x_430 = 0;
x_431 = 0;
x_432 = 0;
x_433 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_433, 0, x_390);
lean_ctor_set(x_433, 1, x_429);
lean_ctor_set_uint8(x_433, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_433, sizeof(void*)*2, x_430);
lean_ctor_set_uint16(x_433, sizeof(void*)*2 + 4, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*2 + 7, x_432);
x_434 = l_Lean_Format_isNil(x_433);
if (x_434 == 0)
{
uint32_t x_435; uint16_t x_436; uint8_t x_437; lean_object* x_438; uint32_t x_439; uint16_t x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_435 = 0;
x_436 = 0;
x_437 = 0;
x_438 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_438, 0, x_433);
lean_ctor_set(x_438, 1, x_376);
lean_ctor_set_uint8(x_438, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_438, sizeof(void*)*2, x_435);
lean_ctor_set_uint16(x_438, sizeof(void*)*2 + 4, x_436);
lean_ctor_set_uint8(x_438, sizeof(void*)*2 + 7, x_437);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_387);
lean_ctor_set_uint8(x_442, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_442, sizeof(void*)*2, x_439);
lean_ctor_set_uint16(x_442, sizeof(void*)*2 + 4, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*2 + 7, x_441);
if (lean_is_scalar(x_347)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_347;
}
lean_ctor_set(x_443, 0, x_389);
lean_ctor_set(x_443, 1, x_442);
if (lean_is_scalar(x_344)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_344;
}
lean_ctor_set(x_444, 0, x_388);
lean_ctor_set(x_444, 1, x_443);
x_7 = x_13;
x_8 = x_444;
goto _start;
}
else
{
uint32_t x_446; uint16_t x_447; uint8_t x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_446 = 0;
x_447 = 0;
x_448 = 0;
x_449 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_449, 0, x_433);
lean_ctor_set(x_449, 1, x_387);
lean_ctor_set_uint8(x_449, sizeof(void*)*2 + 6, x_359);
lean_ctor_set_uint32(x_449, sizeof(void*)*2, x_446);
lean_ctor_set_uint16(x_449, sizeof(void*)*2 + 4, x_447);
lean_ctor_set_uint8(x_449, sizeof(void*)*2 + 7, x_448);
if (lean_is_scalar(x_347)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_347;
}
lean_ctor_set(x_450, 0, x_389);
lean_ctor_set(x_450, 1, x_449);
if (lean_is_scalar(x_344)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_344;
}
lean_ctor_set(x_451, 0, x_388);
lean_ctor_set(x_451, 1, x_450);
x_7 = x_13;
x_8 = x_451;
goto _start;
}
}
}
}
}
else
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_11, 0);
lean_inc(x_484);
lean_dec(x_11);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_485 = lean_ctor_get(x_8, 0);
lean_inc(x_485);
lean_dec(x_8);
x_486 = lean_ctor_get(x_15, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_15, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_488 = x_15;
} else {
 lean_dec_ref(x_15);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_484, 2);
lean_inc(x_489);
x_490 = lean_ctor_get(x_484, 3);
lean_inc(x_490);
lean_dec(x_484);
lean_inc(x_2);
x_491 = l_Lean_MetavarContext_instantiateMVars(x_2, x_490);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_485);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_492);
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_493;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_488;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_496);
x_7 = x_13;
x_8 = x_497;
goto _start;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_499 = lean_ctor_get(x_491, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_500 = x_491;
} else {
 lean_dec_ref(x_491);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_486, 0);
lean_inc(x_501);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_502 = x_486;
} else {
 lean_dec_ref(x_486);
 x_502 = lean_box(0);
}
x_503 = lean_expr_eqv(x_501, x_499);
if (x_503 == 0)
{
uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = l_Lean_Format_isNil(x_487);
x_505 = lean_box(0);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_489);
lean_ctor_set(x_506, 1, x_505);
if (lean_is_scalar(x_502)) {
 x_507 = lean_alloc_ctor(1, 1, 0);
} else {
 x_507 = x_502;
}
lean_ctor_set(x_507, 0, x_499);
if (x_504 == 0)
{
uint8_t x_508; lean_object* x_509; uint32_t x_510; uint16_t x_511; uint8_t x_512; lean_object* x_513; 
x_508 = 0;
x_509 = lean_box(1);
x_510 = 0;
x_511 = 0;
x_512 = 0;
x_513 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_513, 0, x_487);
lean_ctor_set(x_513, 1, x_509);
lean_ctor_set_uint8(x_513, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_513, sizeof(void*)*2, x_510);
lean_ctor_set_uint16(x_513, sizeof(void*)*2 + 4, x_511);
lean_ctor_set_uint8(x_513, sizeof(void*)*2 + 7, x_512);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_501);
if (lean_is_scalar(x_500)) {
 x_514 = lean_alloc_ctor(0, 2, 0);
} else {
 x_514 = x_500;
}
lean_ctor_set(x_514, 0, x_507);
lean_ctor_set(x_514, 1, x_513);
if (lean_is_scalar(x_488)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_488;
}
lean_ctor_set(x_515, 0, x_506);
lean_ctor_set(x_515, 1, x_514);
x_7 = x_13;
x_8 = x_515;
goto _start;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint32_t x_521; uint16_t x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint32_t x_532; uint16_t x_533; uint8_t x_534; lean_object* x_535; lean_object* x_536; uint32_t x_537; uint16_t x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_517 = l_List_reverse___rarg(x_485);
x_518 = l_Lean_Format_flatten___main___closed__1;
x_519 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_517, x_518);
x_520 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_521 = 0;
x_522 = 0;
x_523 = 0;
x_524 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_524, 0, x_519);
lean_ctor_set(x_524, 1, x_520);
lean_ctor_set_uint8(x_524, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_524, sizeof(void*)*2, x_521);
lean_ctor_set_uint16(x_524, sizeof(void*)*2 + 4, x_522);
lean_ctor_set_uint8(x_524, sizeof(void*)*2 + 7, x_523);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_525 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_501);
x_526 = 0;
x_527 = 0;
x_528 = 0;
x_529 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_529, 0, x_509);
lean_ctor_set(x_529, 1, x_525);
lean_ctor_set_uint8(x_529, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_529, sizeof(void*)*2, x_526);
lean_ctor_set_uint16(x_529, sizeof(void*)*2 + 4, x_527);
lean_ctor_set_uint8(x_529, sizeof(void*)*2 + 7, x_528);
x_530 = lean_unsigned_to_nat(2u);
x_531 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_529);
x_532 = 0;
x_533 = 0;
x_534 = 0;
x_535 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_535, 0, x_524);
lean_ctor_set(x_535, 1, x_531);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_535, sizeof(void*)*2, x_532);
lean_ctor_set_uint16(x_535, sizeof(void*)*2 + 4, x_533);
lean_ctor_set_uint8(x_535, sizeof(void*)*2 + 7, x_534);
x_536 = lean_format_group(x_535);
x_537 = 0;
x_538 = 0;
x_539 = 0;
x_540 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_540, 0, x_513);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 6, x_508);
lean_ctor_set_uint32(x_540, sizeof(void*)*2, x_537);
lean_ctor_set_uint16(x_540, sizeof(void*)*2 + 4, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 7, x_539);
if (lean_is_scalar(x_500)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_500;
}
lean_ctor_set(x_541, 0, x_507);
lean_ctor_set(x_541, 1, x_540);
if (lean_is_scalar(x_488)) {
 x_542 = lean_alloc_ctor(0, 2, 0);
} else {
 x_542 = x_488;
}
lean_ctor_set(x_542, 0, x_506);
lean_ctor_set(x_542, 1, x_541);
x_7 = x_13;
x_8 = x_542;
goto _start;
}
}
else
{
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_544; lean_object* x_545; 
lean_dec(x_501);
if (lean_is_scalar(x_500)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_500;
}
lean_ctor_set(x_544, 0, x_507);
lean_ctor_set(x_544, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_545 = lean_alloc_ctor(0, 2, 0);
} else {
 x_545 = x_488;
}
lean_ctor_set(x_545, 0, x_506);
lean_ctor_set(x_545, 1, x_544);
x_7 = x_13;
x_8 = x_545;
goto _start;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; uint32_t x_552; uint16_t x_553; uint8_t x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint32_t x_564; uint16_t x_565; uint8_t x_566; lean_object* x_567; lean_object* x_568; uint32_t x_569; uint16_t x_570; uint8_t x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_547 = l_List_reverse___rarg(x_485);
x_548 = l_Lean_Format_flatten___main___closed__1;
x_549 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_547, x_548);
x_550 = 0;
x_551 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_552 = 0;
x_553 = 0;
x_554 = 0;
x_555 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_555, 0, x_549);
lean_ctor_set(x_555, 1, x_551);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_555, sizeof(void*)*2, x_552);
lean_ctor_set_uint16(x_555, sizeof(void*)*2 + 4, x_553);
lean_ctor_set_uint8(x_555, sizeof(void*)*2 + 7, x_554);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_556 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_501);
x_557 = lean_box(1);
x_558 = 0;
x_559 = 0;
x_560 = 0;
x_561 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_561, 0, x_557);
lean_ctor_set(x_561, 1, x_556);
lean_ctor_set_uint8(x_561, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_561, sizeof(void*)*2, x_558);
lean_ctor_set_uint16(x_561, sizeof(void*)*2 + 4, x_559);
lean_ctor_set_uint8(x_561, sizeof(void*)*2 + 7, x_560);
x_562 = lean_unsigned_to_nat(2u);
x_563 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_563, 0, x_562);
lean_ctor_set(x_563, 1, x_561);
x_564 = 0;
x_565 = 0;
x_566 = 0;
x_567 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_567, 0, x_555);
lean_ctor_set(x_567, 1, x_563);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_567, sizeof(void*)*2, x_564);
lean_ctor_set_uint16(x_567, sizeof(void*)*2 + 4, x_565);
lean_ctor_set_uint8(x_567, sizeof(void*)*2 + 7, x_566);
x_568 = lean_format_group(x_567);
x_569 = 0;
x_570 = 0;
x_571 = 0;
x_572 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_572, 0, x_487);
lean_ctor_set(x_572, 1, x_568);
lean_ctor_set_uint8(x_572, sizeof(void*)*2 + 6, x_550);
lean_ctor_set_uint32(x_572, sizeof(void*)*2, x_569);
lean_ctor_set_uint16(x_572, sizeof(void*)*2 + 4, x_570);
lean_ctor_set_uint8(x_572, sizeof(void*)*2 + 7, x_571);
if (lean_is_scalar(x_500)) {
 x_573 = lean_alloc_ctor(0, 2, 0);
} else {
 x_573 = x_500;
}
lean_ctor_set(x_573, 0, x_507);
lean_ctor_set(x_573, 1, x_572);
if (lean_is_scalar(x_488)) {
 x_574 = lean_alloc_ctor(0, 2, 0);
} else {
 x_574 = x_488;
}
lean_ctor_set(x_574, 0, x_506);
lean_ctor_set(x_574, 1, x_573);
x_7 = x_13;
x_8 = x_574;
goto _start;
}
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_501);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_489);
lean_ctor_set(x_576, 1, x_485);
if (lean_is_scalar(x_502)) {
 x_577 = lean_alloc_ctor(1, 1, 0);
} else {
 x_577 = x_502;
}
lean_ctor_set(x_577, 0, x_499);
if (lean_is_scalar(x_500)) {
 x_578 = lean_alloc_ctor(0, 2, 0);
} else {
 x_578 = x_500;
}
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_578, 1, x_487);
if (lean_is_scalar(x_488)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_488;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_578);
x_7 = x_13;
x_8 = x_579;
goto _start;
}
}
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; uint8_t x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; uint32_t x_599; uint16_t x_600; uint8_t x_601; lean_object* x_602; lean_object* x_603; uint32_t x_604; uint16_t x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; uint32_t x_609; uint16_t x_610; uint8_t x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint32_t x_621; uint16_t x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_581 = lean_ctor_get(x_8, 0);
lean_inc(x_581);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_582 = x_8;
} else {
 lean_dec_ref(x_8);
 x_582 = lean_box(0);
}
x_583 = lean_ctor_get(x_15, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_15, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_585 = x_15;
} else {
 lean_dec_ref(x_15);
 x_585 = lean_box(0);
}
x_586 = lean_ctor_get(x_484, 2);
lean_inc(x_586);
x_587 = lean_ctor_get(x_484, 3);
lean_inc(x_587);
x_588 = lean_ctor_get(x_484, 4);
lean_inc(x_588);
lean_dec(x_484);
x_589 = l_Lean_Format_isNil(x_584);
lean_inc(x_2);
x_590 = l_Lean_MetavarContext_instantiateMVars(x_2, x_587);
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec(x_590);
lean_inc(x_2);
x_592 = l_Lean_MetavarContext_instantiateMVars(x_2, x_588);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec(x_592);
x_594 = l_Lean_Name_toString___closed__1;
x_595 = l_Lean_Name_toStringWithSep___main(x_594, x_586);
x_596 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_596, 0, x_595);
x_597 = 0;
x_598 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__4;
x_599 = 0;
x_600 = 0;
x_601 = 0;
x_602 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_598);
lean_ctor_set_uint8(x_602, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_602, sizeof(void*)*2, x_599);
lean_ctor_set_uint16(x_602, sizeof(void*)*2 + 4, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*2 + 7, x_601);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_603 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_591);
x_604 = 0;
x_605 = 0;
x_606 = 0;
x_607 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_607, 0, x_602);
lean_ctor_set(x_607, 1, x_603);
lean_ctor_set_uint8(x_607, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_607, sizeof(void*)*2, x_604);
lean_ctor_set_uint16(x_607, sizeof(void*)*2 + 4, x_605);
lean_ctor_set_uint8(x_607, sizeof(void*)*2 + 7, x_606);
x_608 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__6;
x_609 = 0;
x_610 = 0;
x_611 = 0;
x_612 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_612, 0, x_607);
lean_ctor_set(x_612, 1, x_608);
lean_ctor_set_uint8(x_612, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_612, sizeof(void*)*2, x_609);
lean_ctor_set_uint16(x_612, sizeof(void*)*2 + 4, x_610);
lean_ctor_set_uint8(x_612, sizeof(void*)*2 + 7, x_611);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_613 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_593);
x_614 = lean_box(1);
x_615 = 0;
x_616 = 0;
x_617 = 0;
x_618 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_618, 0, x_614);
lean_ctor_set(x_618, 1, x_613);
lean_ctor_set_uint8(x_618, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_618, sizeof(void*)*2, x_615);
lean_ctor_set_uint16(x_618, sizeof(void*)*2 + 4, x_616);
lean_ctor_set_uint8(x_618, sizeof(void*)*2 + 7, x_617);
x_619 = lean_unsigned_to_nat(2u);
x_620 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_618);
x_621 = 0;
x_622 = 0;
x_623 = 0;
x_624 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_624, 0, x_612);
lean_ctor_set(x_624, 1, x_620);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_624, sizeof(void*)*2, x_621);
lean_ctor_set_uint16(x_624, sizeof(void*)*2 + 4, x_622);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 7, x_623);
x_625 = lean_format_group(x_624);
x_626 = lean_box(0);
x_627 = lean_box(0);
if (x_589 == 0)
{
uint32_t x_692; uint16_t x_693; uint8_t x_694; lean_object* x_695; 
x_692 = 0;
x_693 = 0;
x_694 = 0;
x_695 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_695, 0, x_584);
lean_ctor_set(x_695, 1, x_614);
lean_ctor_set_uint8(x_695, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_695, sizeof(void*)*2, x_692);
lean_ctor_set_uint16(x_695, sizeof(void*)*2 + 4, x_693);
lean_ctor_set_uint8(x_695, sizeof(void*)*2 + 7, x_694);
if (lean_obj_tag(x_581) == 0)
{
uint8_t x_696; 
lean_dec(x_585);
lean_dec(x_583);
lean_dec(x_582);
x_696 = l_Lean_Format_isNil(x_695);
if (x_696 == 0)
{
uint32_t x_697; uint16_t x_698; uint8_t x_699; lean_object* x_700; uint32_t x_701; uint16_t x_702; uint8_t x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_697 = 0;
x_698 = 0;
x_699 = 0;
x_700 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_700, 0, x_695);
lean_ctor_set(x_700, 1, x_614);
lean_ctor_set_uint8(x_700, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_700, sizeof(void*)*2, x_697);
lean_ctor_set_uint16(x_700, sizeof(void*)*2 + 4, x_698);
lean_ctor_set_uint8(x_700, sizeof(void*)*2 + 7, x_699);
x_701 = 0;
x_702 = 0;
x_703 = 0;
x_704 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_704, 0, x_700);
lean_ctor_set(x_704, 1, x_625);
lean_ctor_set_uint8(x_704, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_704, sizeof(void*)*2, x_701);
lean_ctor_set_uint16(x_704, sizeof(void*)*2 + 4, x_702);
lean_ctor_set_uint8(x_704, sizeof(void*)*2 + 7, x_703);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_627);
lean_ctor_set(x_705, 1, x_704);
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_626);
lean_ctor_set(x_706, 1, x_705);
x_7 = x_13;
x_8 = x_706;
goto _start;
}
else
{
uint32_t x_708; uint16_t x_709; uint8_t x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_708 = 0;
x_709 = 0;
x_710 = 0;
x_711 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_711, 0, x_695);
lean_ctor_set(x_711, 1, x_625);
lean_ctor_set_uint8(x_711, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_711, sizeof(void*)*2, x_708);
lean_ctor_set_uint16(x_711, sizeof(void*)*2 + 4, x_709);
lean_ctor_set_uint8(x_711, sizeof(void*)*2 + 7, x_710);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_627);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_626);
lean_ctor_set(x_713, 1, x_712);
x_7 = x_13;
x_8 = x_713;
goto _start;
}
}
else
{
x_628 = x_695;
goto block_691;
}
}
else
{
if (lean_obj_tag(x_581) == 0)
{
uint32_t x_715; uint16_t x_716; uint8_t x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_585);
lean_dec(x_583);
lean_dec(x_582);
x_715 = 0;
x_716 = 0;
x_717 = 0;
x_718 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_718, 0, x_584);
lean_ctor_set(x_718, 1, x_625);
lean_ctor_set_uint8(x_718, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_718, sizeof(void*)*2, x_715);
lean_ctor_set_uint16(x_718, sizeof(void*)*2 + 4, x_716);
lean_ctor_set_uint8(x_718, sizeof(void*)*2 + 7, x_717);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_627);
lean_ctor_set(x_719, 1, x_718);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_626);
lean_ctor_set(x_720, 1, x_719);
x_7 = x_13;
x_8 = x_720;
goto _start;
}
else
{
x_628 = x_584;
goto block_691;
}
}
block_691:
{
if (lean_obj_tag(x_583) == 0)
{
uint8_t x_629; 
lean_dec(x_581);
x_629 = l_Lean_Format_isNil(x_628);
if (x_629 == 0)
{
uint32_t x_630; uint16_t x_631; uint8_t x_632; lean_object* x_633; uint32_t x_634; uint16_t x_635; uint8_t x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_630 = 0;
x_631 = 0;
x_632 = 0;
x_633 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_633, 0, x_628);
lean_ctor_set(x_633, 1, x_614);
lean_ctor_set_uint8(x_633, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_633, sizeof(void*)*2, x_630);
lean_ctor_set_uint16(x_633, sizeof(void*)*2 + 4, x_631);
lean_ctor_set_uint8(x_633, sizeof(void*)*2 + 7, x_632);
x_634 = 0;
x_635 = 0;
x_636 = 0;
x_637 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_637, 0, x_633);
lean_ctor_set(x_637, 1, x_625);
lean_ctor_set_uint8(x_637, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_637, sizeof(void*)*2, x_634);
lean_ctor_set_uint16(x_637, sizeof(void*)*2 + 4, x_635);
lean_ctor_set_uint8(x_637, sizeof(void*)*2 + 7, x_636);
if (lean_is_scalar(x_585)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_585;
}
lean_ctor_set(x_638, 0, x_627);
lean_ctor_set(x_638, 1, x_637);
if (lean_is_scalar(x_582)) {
 x_639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_639 = x_582;
}
lean_ctor_set(x_639, 0, x_626);
lean_ctor_set(x_639, 1, x_638);
x_7 = x_13;
x_8 = x_639;
goto _start;
}
else
{
uint32_t x_641; uint16_t x_642; uint8_t x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_641 = 0;
x_642 = 0;
x_643 = 0;
x_644 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_644, 0, x_628);
lean_ctor_set(x_644, 1, x_625);
lean_ctor_set_uint8(x_644, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_644, sizeof(void*)*2, x_641);
lean_ctor_set_uint16(x_644, sizeof(void*)*2 + 4, x_642);
lean_ctor_set_uint8(x_644, sizeof(void*)*2 + 7, x_643);
if (lean_is_scalar(x_585)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_585;
}
lean_ctor_set(x_645, 0, x_627);
lean_ctor_set(x_645, 1, x_644);
if (lean_is_scalar(x_582)) {
 x_646 = lean_alloc_ctor(0, 2, 0);
} else {
 x_646 = x_582;
}
lean_ctor_set(x_646, 0, x_626);
lean_ctor_set(x_646, 1, x_645);
x_7 = x_13;
x_8 = x_646;
goto _start;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint32_t x_653; uint16_t x_654; uint8_t x_655; lean_object* x_656; lean_object* x_657; uint32_t x_658; uint16_t x_659; uint8_t x_660; lean_object* x_661; lean_object* x_662; uint32_t x_663; uint16_t x_664; uint8_t x_665; lean_object* x_666; lean_object* x_667; uint32_t x_668; uint16_t x_669; uint8_t x_670; lean_object* x_671; uint8_t x_672; 
x_648 = lean_ctor_get(x_583, 0);
lean_inc(x_648);
lean_dec(x_583);
x_649 = l_List_reverse___rarg(x_581);
x_650 = l_Lean_Format_flatten___main___closed__1;
x_651 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_649, x_650);
x_652 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_653 = 0;
x_654 = 0;
x_655 = 0;
x_656 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_656, 0, x_651);
lean_ctor_set(x_656, 1, x_652);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_656, sizeof(void*)*2, x_653);
lean_ctor_set_uint16(x_656, sizeof(void*)*2 + 4, x_654);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 7, x_655);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_657 = l_Lean_ppExpr(x_1, x_2, x_4, x_3, x_648);
x_658 = 0;
x_659 = 0;
x_660 = 0;
x_661 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_661, 0, x_614);
lean_ctor_set(x_661, 1, x_657);
lean_ctor_set_uint8(x_661, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_661, sizeof(void*)*2, x_658);
lean_ctor_set_uint16(x_661, sizeof(void*)*2 + 4, x_659);
lean_ctor_set_uint8(x_661, sizeof(void*)*2 + 7, x_660);
x_662 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_662, 0, x_619);
lean_ctor_set(x_662, 1, x_661);
x_663 = 0;
x_664 = 0;
x_665 = 0;
x_666 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_666, 0, x_656);
lean_ctor_set(x_666, 1, x_662);
lean_ctor_set_uint8(x_666, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_666, sizeof(void*)*2, x_663);
lean_ctor_set_uint16(x_666, sizeof(void*)*2 + 4, x_664);
lean_ctor_set_uint8(x_666, sizeof(void*)*2 + 7, x_665);
x_667 = lean_format_group(x_666);
x_668 = 0;
x_669 = 0;
x_670 = 0;
x_671 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_671, 0, x_628);
lean_ctor_set(x_671, 1, x_667);
lean_ctor_set_uint8(x_671, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_671, sizeof(void*)*2, x_668);
lean_ctor_set_uint16(x_671, sizeof(void*)*2 + 4, x_669);
lean_ctor_set_uint8(x_671, sizeof(void*)*2 + 7, x_670);
x_672 = l_Lean_Format_isNil(x_671);
if (x_672 == 0)
{
uint32_t x_673; uint16_t x_674; uint8_t x_675; lean_object* x_676; uint32_t x_677; uint16_t x_678; uint8_t x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_673 = 0;
x_674 = 0;
x_675 = 0;
x_676 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_676, 0, x_671);
lean_ctor_set(x_676, 1, x_614);
lean_ctor_set_uint8(x_676, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_676, sizeof(void*)*2, x_673);
lean_ctor_set_uint16(x_676, sizeof(void*)*2 + 4, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*2 + 7, x_675);
x_677 = 0;
x_678 = 0;
x_679 = 0;
x_680 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_680, 0, x_676);
lean_ctor_set(x_680, 1, x_625);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_680, sizeof(void*)*2, x_677);
lean_ctor_set_uint16(x_680, sizeof(void*)*2 + 4, x_678);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 7, x_679);
if (lean_is_scalar(x_585)) {
 x_681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_681 = x_585;
}
lean_ctor_set(x_681, 0, x_627);
lean_ctor_set(x_681, 1, x_680);
if (lean_is_scalar(x_582)) {
 x_682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_682 = x_582;
}
lean_ctor_set(x_682, 0, x_626);
lean_ctor_set(x_682, 1, x_681);
x_7 = x_13;
x_8 = x_682;
goto _start;
}
else
{
uint32_t x_684; uint16_t x_685; uint8_t x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_684 = 0;
x_685 = 0;
x_686 = 0;
x_687 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_687, 0, x_671);
lean_ctor_set(x_687, 1, x_625);
lean_ctor_set_uint8(x_687, sizeof(void*)*2 + 6, x_597);
lean_ctor_set_uint32(x_687, sizeof(void*)*2, x_684);
lean_ctor_set_uint16(x_687, sizeof(void*)*2 + 4, x_685);
lean_ctor_set_uint8(x_687, sizeof(void*)*2 + 7, x_686);
if (lean_is_scalar(x_585)) {
 x_688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_688 = x_585;
}
lean_ctor_set(x_688, 0, x_627);
lean_ctor_set(x_688, 1, x_687);
if (lean_is_scalar(x_582)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_582;
}
lean_ctor_set(x_689, 0, x_626);
lean_ctor_set(x_689, 1, x_688);
x_7 = x_13;
x_8 = x_689;
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
uint8_t x_98; lean_object* x_99; uint32_t x_100; uint16_t x_101; uint8_t x_102; lean_object* x_103; 
x_98 = 0;
x_99 = lean_box(1);
x_100 = 0;
x_101 = 0;
x_102 = 0;
x_103 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_103, 0, x_14);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 6, x_98);
lean_ctor_set_uint32(x_103, sizeof(void*)*2, x_100);
lean_ctor_set_uint16(x_103, sizeof(void*)*2 + 4, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*2 + 7, x_102);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_103;
goto block_97;
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
x_21 = x_103;
goto block_97;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint32_t x_109; uint16_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; uint32_t x_114; uint16_t x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; uint32_t x_119; uint16_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; uint32_t x_124; uint16_t x_125; uint8_t x_126; lean_object* x_127; 
x_104 = lean_ctor_get(x_13, 0);
lean_inc(x_104);
lean_dec(x_13);
x_105 = l_List_reverse___rarg(x_12);
x_106 = l_Lean_Format_flatten___main___closed__1;
x_107 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_105, x_106);
x_108 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_109 = 0;
x_110 = 0;
x_111 = 0;
x_112 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_112, 0, x_107);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set_uint8(x_112, sizeof(void*)*2 + 6, x_98);
lean_ctor_set_uint32(x_112, sizeof(void*)*2, x_109);
lean_ctor_set_uint16(x_112, sizeof(void*)*2 + 4, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*2 + 7, x_111);
x_113 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_104);
x_114 = 0;
x_115 = 0;
x_116 = 0;
x_117 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_117, 0, x_99);
lean_ctor_set(x_117, 1, x_113);
lean_ctor_set_uint8(x_117, sizeof(void*)*2 + 6, x_98);
lean_ctor_set_uint32(x_117, sizeof(void*)*2, x_114);
lean_ctor_set_uint16(x_117, sizeof(void*)*2 + 4, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*2 + 7, x_116);
x_118 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_118, 0, x_18);
lean_ctor_set(x_118, 1, x_117);
x_119 = 0;
x_120 = 0;
x_121 = 0;
x_122 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_118);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 6, x_98);
lean_ctor_set_uint32(x_122, sizeof(void*)*2, x_119);
lean_ctor_set_uint16(x_122, sizeof(void*)*2 + 4, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*2 + 7, x_121);
x_123 = lean_format_group(x_122);
x_124 = 0;
x_125 = 0;
x_126 = 0;
x_127 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_127, 0, x_103);
lean_ctor_set(x_127, 1, x_123);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 6, x_98);
lean_ctor_set_uint32(x_127, sizeof(void*)*2, x_124);
lean_ctor_set_uint16(x_127, sizeof(void*)*2 + 4, x_125);
lean_ctor_set_uint8(x_127, sizeof(void*)*2 + 7, x_126);
x_21 = x_127;
goto block_97;
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
goto block_97;
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
goto block_97;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; uint32_t x_134; uint16_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint32_t x_140; uint16_t x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; uint32_t x_145; uint16_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; lean_object* x_153; 
x_128 = lean_ctor_get(x_13, 0);
lean_inc(x_128);
lean_dec(x_13);
x_129 = l_List_reverse___rarg(x_12);
x_130 = l_Lean_Format_flatten___main___closed__1;
x_131 = l_Lean_Format_joinSep___main___at_Lean_ppGoal___spec__1(x_129, x_130);
x_132 = 0;
x_133 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__2;
x_134 = 0;
x_135 = 0;
x_136 = 0;
x_137 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_137, 0, x_131);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set_uint8(x_137, sizeof(void*)*2 + 6, x_132);
lean_ctor_set_uint32(x_137, sizeof(void*)*2, x_134);
lean_ctor_set_uint16(x_137, sizeof(void*)*2 + 4, x_135);
lean_ctor_set_uint8(x_137, sizeof(void*)*2 + 7, x_136);
x_138 = l_Lean_ppExpr(x_1, x_2, x_8, x_3, x_128);
x_139 = lean_box(1);
x_140 = 0;
x_141 = 0;
x_142 = 0;
x_143 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set_uint8(x_143, sizeof(void*)*2 + 6, x_132);
lean_ctor_set_uint32(x_143, sizeof(void*)*2, x_140);
lean_ctor_set_uint16(x_143, sizeof(void*)*2 + 4, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*2 + 7, x_142);
x_144 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_144, 0, x_18);
lean_ctor_set(x_144, 1, x_143);
x_145 = 0;
x_146 = 0;
x_147 = 0;
x_148 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_148, 0, x_137);
lean_ctor_set(x_148, 1, x_144);
lean_ctor_set_uint8(x_148, sizeof(void*)*2 + 6, x_132);
lean_ctor_set_uint32(x_148, sizeof(void*)*2, x_145);
lean_ctor_set_uint16(x_148, sizeof(void*)*2 + 4, x_146);
lean_ctor_set_uint8(x_148, sizeof(void*)*2 + 7, x_147);
x_149 = lean_format_group(x_148);
x_150 = 0;
x_151 = 0;
x_152 = 0;
x_153 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_153, 0, x_14);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set_uint8(x_153, sizeof(void*)*2 + 6, x_132);
lean_ctor_set_uint32(x_153, sizeof(void*)*2, x_150);
lean_ctor_set_uint16(x_153, sizeof(void*)*2 + 4, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*2 + 7, x_152);
x_21 = x_153;
goto block_97;
}
}
}
block_97:
{
uint8_t x_22; 
x_22 = l_Lean_Format_isNil(x_21);
if (x_22 == 0)
{
uint8_t x_23; lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint16_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint32_t x_35; uint16_t x_36; uint8_t x_37; lean_object* x_38; uint32_t x_39; uint16_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_23 = 0;
x_24 = lean_box(1);
x_25 = 0;
x_26 = 0;
x_27 = 0;
x_28 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_25);
lean_ctor_set_uint16(x_28, sizeof(void*)*2 + 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 7, x_27);
x_29 = l_Lean_ppGoal___closed__6;
x_30 = 0;
x_31 = 0;
x_32 = 0;
x_33 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_33, sizeof(void*)*2, x_30);
lean_ctor_set_uint16(x_33, sizeof(void*)*2 + 4, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*2 + 7, x_32);
x_34 = l_Lean_Format_flatten___main___closed__1;
x_35 = 0;
x_36 = 0;
x_37 = 0;
x_38 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_38, sizeof(void*)*2, x_35);
lean_ctor_set_uint16(x_38, sizeof(void*)*2 + 4, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 7, x_37);
x_39 = 0;
x_40 = 0;
x_41 = 0;
x_42 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_uint16(x_42, sizeof(void*)*2 + 4, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 7, x_41);
if (lean_obj_tag(x_20) == 0)
{
return x_42;
}
else
{
lean_object* x_61; 
x_61 = lean_box(0);
x_43 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; uint16_t x_49; uint8_t x_50; lean_object* x_51; uint32_t x_52; uint16_t x_53; uint8_t x_54; lean_object* x_55; uint32_t x_56; uint16_t x_57; uint8_t x_58; lean_object* x_59; 
lean_dec(x_43);
x_44 = l_Lean_Name_toString___closed__1;
x_45 = l_Lean_Name_toStringWithSep___main(x_44, x_20);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_ppGoal___closed__8;
x_48 = 0;
x_49 = 0;
x_50 = 0;
x_51 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_51, sizeof(void*)*2, x_48);
lean_ctor_set_uint16(x_51, sizeof(void*)*2 + 4, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*2 + 7, x_50);
x_52 = 0;
x_53 = 0;
x_54 = 0;
x_55 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_24);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_uint16(x_55, sizeof(void*)*2 + 4, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 7, x_54);
x_56 = 0;
x_57 = 0;
x_58 = 0;
x_59 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_42);
lean_ctor_set_uint8(x_59, sizeof(void*)*2 + 6, x_23);
lean_ctor_set_uint32(x_59, sizeof(void*)*2, x_56);
lean_ctor_set_uint16(x_59, sizeof(void*)*2 + 4, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*2 + 7, x_58);
return x_59;
}
}
else
{
uint8_t x_62; lean_object* x_63; uint32_t x_64; uint16_t x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; uint16_t x_70; uint8_t x_71; lean_object* x_72; uint32_t x_73; uint16_t x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_62 = 0;
x_63 = l_Lean_ppGoal___closed__6;
x_64 = 0;
x_65 = 0;
x_66 = 0;
x_67 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_67, 0, x_21);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_67, sizeof(void*)*2, x_64);
lean_ctor_set_uint16(x_67, sizeof(void*)*2 + 4, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*2 + 7, x_66);
x_68 = l_Lean_Format_flatten___main___closed__1;
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_uint16(x_72, sizeof(void*)*2 + 4, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 7, x_71);
x_73 = 0;
x_74 = 0;
x_75 = 0;
x_76 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_19);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_76, sizeof(void*)*2, x_73);
lean_ctor_set_uint16(x_76, sizeof(void*)*2 + 4, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 7, x_75);
if (lean_obj_tag(x_20) == 0)
{
return x_76;
}
else
{
lean_object* x_96; 
x_96 = lean_box(0);
x_77 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint32_t x_82; uint16_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint32_t x_87; uint16_t x_88; uint8_t x_89; lean_object* x_90; uint32_t x_91; uint16_t x_92; uint8_t x_93; lean_object* x_94; 
lean_dec(x_77);
x_78 = l_Lean_Name_toString___closed__1;
x_79 = l_Lean_Name_toStringWithSep___main(x_78, x_20);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_Lean_ppGoal___closed__8;
x_82 = 0;
x_83 = 0;
x_84 = 0;
x_85 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_80);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_85, sizeof(void*)*2, x_82);
lean_ctor_set_uint16(x_85, sizeof(void*)*2 + 4, x_83);
lean_ctor_set_uint8(x_85, sizeof(void*)*2 + 7, x_84);
x_86 = lean_box(1);
x_87 = 0;
x_88 = 0;
x_89 = 0;
x_90 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_90, sizeof(void*)*2, x_87);
lean_ctor_set_uint16(x_90, sizeof(void*)*2 + 4, x_88);
lean_ctor_set_uint8(x_90, sizeof(void*)*2 + 7, x_89);
x_91 = 0;
x_92 = 0;
x_93 = 0;
x_94 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_76);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 6, x_62);
lean_ctor_set_uint32(x_94, sizeof(void*)*2, x_91);
lean_ctor_set_uint16(x_94, sizeof(void*)*2 + 4, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 7, x_93);
return x_94;
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
