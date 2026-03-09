// Lean compiler output
// Module: Lean.Meta.Match.Value
// Imports: public import Lean.Meta.LitValues
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(x_1, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_9 = l_Lean_Meta_getNatValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_182; 
x_10 = lean_ctor_get(x_9, 0);
x_182 = !lean_is_exclusive(x_9);
if (x_182 == 0)
{
x_11 = x_9;
x_12 = x_182;
goto block_181;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_182;
goto block_181;
}
block_181:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; 
lean_del_object(x_11);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_13 = l_Lean_Meta_getIntValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_167; 
x_14 = lean_ctor_get(x_13, 0);
x_167 = !lean_is_exclusive(x_13);
if (x_167 == 0)
{
x_15 = x_13;
x_16 = x_167;
goto block_166;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_167;
goto block_166;
}
block_166:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; 
lean_del_object(x_15);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_17 = l_Lean_Meta_getFinValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_152; 
x_18 = lean_ctor_get(x_17, 0);
x_152 = !lean_is_exclusive(x_17);
if (x_152 == 0)
{
x_19 = x_17;
x_20 = x_152;
goto block_151;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_152;
goto block_151;
}
block_151:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; 
lean_del_object(x_19);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_21 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_137; 
x_22 = lean_ctor_get(x_21, 0);
x_137 = !lean_is_exclusive(x_21);
if (x_137 == 0)
{
x_23 = x_21;
x_24 = x_137;
goto block_136;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_137;
goto block_136;
}
block_136:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_25; 
lean_inc(x_8);
x_25 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_del_object(x_23);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_26 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_117; 
x_27 = lean_ctor_get(x_26, 0);
x_117 = !lean_is_exclusive(x_26);
if (x_117 == 0)
{
x_28 = x_26;
x_29 = x_117;
goto block_116;
}
else
{
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_29 = x_117;
goto block_116;
}
block_116:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; 
lean_del_object(x_28);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_30 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_102; 
x_31 = lean_ctor_get(x_30, 0);
x_102 = !lean_is_exclusive(x_30);
if (x_102 == 0)
{
x_32 = x_30;
x_33 = x_102;
goto block_101;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_102;
goto block_101;
}
block_101:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; 
lean_del_object(x_32);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_34 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_87; 
x_35 = lean_ctor_get(x_34, 0);
x_87 = !lean_is_exclusive(x_34);
if (x_87 == 0)
{
x_36 = x_34;
x_37 = x_87;
goto block_86;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_87;
goto block_86;
}
block_86:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_38; 
lean_del_object(x_36);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_38 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_72; 
x_39 = lean_ctor_get(x_38, 0);
x_72 = !lean_is_exclusive(x_38);
if (x_72 == 0)
{
x_40 = x_38;
x_41 = x_72;
goto block_71;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_72;
goto block_71;
}
block_71:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_42; 
lean_del_object(x_40);
x_42 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_57; 
x_43 = lean_ctor_get(x_42, 0);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
x_44 = x_42;
x_45 = x_57;
goto block_56;
}
else
{
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_box(0);
x_45 = x_57;
goto block_56;
}
block_56:
{
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = 0;
x_47 = lean_box(x_46);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_47);
x_48 = x_44;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
else
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_43);
x_51 = 1;
x_52 = lean_box(x_51);
if (x_45 == 0)
{
lean_ctor_set(x_44, 0, x_52);
x_53 = x_44;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_52);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
x_58 = lean_ctor_get(x_42, 0);
x_65 = !lean_is_exclusive(x_42);
if (x_65 == 0)
{
x_59 = x_42;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_42);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_39);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = 1;
x_67 = lean_box(x_66);
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_67);
x_68 = x_40;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_67);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_73 = lean_ctor_get(x_38, 0);
x_80 = !lean_is_exclusive(x_38);
if (x_80 == 0)
{
x_74 = x_38;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_38);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_35);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = 1;
x_82 = lean_box(x_81);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_82);
x_83 = x_36;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_82);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_95; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_34, 0);
x_95 = !lean_is_exclusive(x_34);
if (x_95 == 0)
{
x_89 = x_34;
x_90 = x_95;
goto block_94;
}
else
{
lean_inc(x_88);
lean_dec(x_34);
x_89 = lean_box(0);
x_90 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_91; 
if (x_90 == 0)
{
x_91 = x_89;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_88);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_31);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_96 = 1;
x_97 = lean_box(x_96);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_97);
x_98 = x_32;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_97);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_103 = lean_ctor_get(x_30, 0);
x_110 = !lean_is_exclusive(x_30);
if (x_110 == 0)
{
x_104 = x_30;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_30);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
else
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_111 = 1;
x_112 = lean_box(x_111);
if (x_29 == 0)
{
lean_ctor_set(x_28, 0, x_112);
x_113 = x_28;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_125; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_118 = lean_ctor_get(x_26, 0);
x_125 = !lean_is_exclusive(x_26);
if (x_125 == 0)
{
x_119 = x_26;
x_120 = x_125;
goto block_124;
}
else
{
lean_inc(x_118);
lean_dec(x_26);
x_119 = lean_box(0);
x_120 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_121; 
if (x_120 == 0)
{
x_121 = x_119;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_118);
x_121 = x_123;
goto block_122;
}
block_122:
{
return x_121;
}
}
}
}
else
{
uint8_t x_126; lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_25);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_126 = 1;
x_127 = lean_box(x_126);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_127);
x_128 = x_23;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_127);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
else
{
uint8_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec_ref(x_22);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_131 = 1;
x_132 = lean_box(x_131);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_132);
x_133 = x_23;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_145; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = lean_ctor_get(x_21, 0);
x_145 = !lean_is_exclusive(x_21);
if (x_145 == 0)
{
x_139 = x_21;
x_140 = x_145;
goto block_144;
}
else
{
lean_inc(x_138);
lean_dec(x_21);
x_139 = lean_box(0);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_140 == 0)
{
x_141 = x_139;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_138);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
else
{
uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec_ref(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_146 = 1;
x_147 = lean_box(x_146);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_147);
x_148 = x_19;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_147);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_153 = lean_ctor_get(x_17, 0);
x_160 = !lean_is_exclusive(x_17);
if (x_160 == 0)
{
x_154 = x_17;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_17);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
else
{
uint8_t x_161; lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_161 = 1;
x_162 = lean_box(x_161);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_162);
x_163 = x_15;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_162);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_175; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_168 = lean_ctor_get(x_13, 0);
x_175 = !lean_is_exclusive(x_13);
if (x_175 == 0)
{
x_169 = x_13;
x_170 = x_175;
goto block_174;
}
else
{
lean_inc(x_168);
lean_dec(x_13);
x_169 = lean_box(0);
x_170 = x_175;
goto block_174;
}
block_174:
{
lean_object* x_171; 
if (x_170 == 0)
{
x_171 = x_169;
goto block_172;
}
else
{
lean_object* x_173; 
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_168);
x_171 = x_173;
goto block_172;
}
block_172:
{
return x_171;
}
}
}
}
else
{
uint8_t x_176; lean_object* x_177; lean_object* x_178; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_176 = 1;
x_177 = lean_box(x_176);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_177);
x_178 = x_11;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_177);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
else
{
lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_190; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_183 = lean_ctor_get(x_9, 0);
x_190 = !lean_is_exclusive(x_9);
if (x_190 == 0)
{
x_184 = x_9;
x_185 = x_190;
goto block_189;
}
else
{
lean_inc(x_183);
lean_dec(x_9);
x_184 = lean_box(0);
x_185 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_186; 
if (x_185 == 0)
{
x_186 = x_184;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_isMatchValue(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_LitValues(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LitValues(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Value(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_Value(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_Value(builtin);
}
#ifdef __cplusplus
}
#endif
