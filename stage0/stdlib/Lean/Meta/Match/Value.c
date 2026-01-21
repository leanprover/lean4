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
lean_object* l_Lean_Meta_getCharValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt64Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt32Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_getStringValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_getUInt8Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUInt16Value_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatchValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFinValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_isMatchValue_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
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
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
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
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_free_object(x_9);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_12 = l_Lean_Meta_getIntValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_free_object(x_12);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_15 = l_Lean_Meta_getFinValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_15);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_18 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_inc(x_8);
x_21 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_free_object(x_18);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_22 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_free_object(x_22);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_25 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_free_object(x_25);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_28 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_free_object(x_28);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_31 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_free_object(x_31);
x_34 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; lean_object* x_38; 
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec_ref(x_36);
x_39 = 1;
x_40 = lean_box(x_39);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_41);
x_45 = 1;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_34, 0);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; lean_object* x_52; 
lean_dec_ref(x_33);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_31, 0, x_52);
return x_31;
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_31, 0);
lean_inc(x_53);
lean_dec(x_31);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_55);
x_60 = 1;
x_61 = lean_box(x_60);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
uint8_t x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_53);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = 1;
x_67 = lean_box(x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_69 = !lean_is_exclusive(x_31);
if (x_69 == 0)
{
return x_31;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_31, 0);
lean_inc(x_70);
lean_dec(x_31);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; lean_object* x_73; 
lean_dec_ref(x_30);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_72 = 1;
x_73 = lean_box(x_72);
lean_ctor_set(x_28, 0, x_73);
return x_28;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_28, 0);
lean_inc(x_74);
lean_dec(x_28);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_75 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_78; 
lean_dec(x_77);
x_78 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_box(x_81);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
else
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_79);
x_84 = 1;
x_85 = lean_box(x_84);
if (lean_is_scalar(x_80)) {
 x_86 = lean_alloc_ctor(0, 1, 0);
} else {
 x_86 = x_80;
}
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_88 = x_78;
} else {
 lean_dec_ref(x_78);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
else
{
uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_76);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_90 = 1;
x_91 = lean_box(x_90);
if (lean_is_scalar(x_77)) {
 x_92 = lean_alloc_ctor(0, 1, 0);
} else {
 x_92 = x_77;
}
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_93 = lean_ctor_get(x_75, 0);
lean_inc(x_93);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_94 = x_75;
} else {
 lean_dec_ref(x_75);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 1, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_93);
return x_95;
}
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; 
lean_dec_ref(x_74);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_96 = 1;
x_97 = lean_box(x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = !lean_is_exclusive(x_28);
if (x_99 == 0)
{
return x_28;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_28, 0);
lean_inc(x_100);
lean_dec(x_28);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; lean_object* x_103; 
lean_dec_ref(x_27);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_102 = 1;
x_103 = lean_box(x_102);
lean_ctor_set(x_25, 0, x_103);
return x_25;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_25, 0);
lean_inc(x_104);
lean_dec(x_25);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_105 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_107 = x_105;
} else {
 lean_dec_ref(x_105);
 x_107 = lean_box(0);
}
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_108; 
lean_dec(x_107);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_108 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_111; 
lean_dec(x_110);
x_111 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_114 = 0;
x_115 = lean_box(x_114);
if (lean_is_scalar(x_113)) {
 x_116 = lean_alloc_ctor(0, 1, 0);
} else {
 x_116 = x_113;
}
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
uint8_t x_117; lean_object* x_118; lean_object* x_119; 
lean_dec_ref(x_112);
x_117 = 1;
x_118 = lean_box(x_117);
if (lean_is_scalar(x_113)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_113;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_111, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
uint8_t x_123; lean_object* x_124; lean_object* x_125; 
lean_dec_ref(x_109);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_123 = 1;
x_124 = lean_box(x_123);
if (lean_is_scalar(x_110)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_110;
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_126 = lean_ctor_get(x_108, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_127 = x_108;
} else {
 lean_dec_ref(x_108);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
else
{
uint8_t x_129; lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_106);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_129 = 1;
x_130 = lean_box(x_129);
if (lean_is_scalar(x_107)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_107;
}
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_132 = lean_ctor_get(x_105, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 x_133 = x_105;
} else {
 lean_dec_ref(x_105);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_132);
return x_134;
}
}
else
{
uint8_t x_135; lean_object* x_136; lean_object* x_137; 
lean_dec_ref(x_104);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = 1;
x_136 = lean_box(x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_138 = !lean_is_exclusive(x_25);
if (x_138 == 0)
{
return x_25;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_25, 0);
lean_inc(x_139);
lean_dec(x_25);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; lean_object* x_142; 
lean_dec_ref(x_24);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_141 = 1;
x_142 = lean_box(x_141);
lean_ctor_set(x_22, 0, x_142);
return x_22;
}
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_22, 0);
lean_inc(x_143);
lean_dec(x_22);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_144 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_147; 
lean_dec(x_146);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_147 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_150; 
lean_dec(x_149);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_150 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_153; 
lean_dec(x_152);
x_153 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_156; lean_object* x_157; lean_object* x_158; 
x_156 = 0;
x_157 = lean_box(x_156);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_154);
x_159 = 1;
x_160 = lean_box(x_159);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_153, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_163 = x_153;
} else {
 lean_dec_ref(x_153);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
else
{
uint8_t x_165; lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_151);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_165 = 1;
x_166 = lean_box(x_165);
if (lean_is_scalar(x_152)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_152;
}
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_168 = lean_ctor_get(x_150, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_169 = x_150;
} else {
 lean_dec_ref(x_150);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
}
else
{
uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_148);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_171 = 1;
x_172 = lean_box(x_171);
if (lean_is_scalar(x_149)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_149;
}
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_174 = lean_ctor_get(x_147, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_175 = x_147;
} else {
 lean_dec_ref(x_147);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 1, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_174);
return x_176;
}
}
else
{
uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec_ref(x_145);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_177 = 1;
x_178 = lean_box(x_177);
if (lean_is_scalar(x_146)) {
 x_179 = lean_alloc_ctor(0, 1, 0);
} else {
 x_179 = x_146;
}
lean_ctor_set(x_179, 0, x_178);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_180 = lean_ctor_get(x_144, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_181 = x_144;
} else {
 lean_dec_ref(x_144);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
else
{
uint8_t x_183; lean_object* x_184; lean_object* x_185; 
lean_dec_ref(x_143);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_183 = 1;
x_184 = lean_box(x_183);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_186 = !lean_is_exclusive(x_22);
if (x_186 == 0)
{
return x_22;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_22, 0);
lean_inc(x_187);
lean_dec(x_22);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
}
else
{
uint8_t x_189; lean_object* x_190; 
lean_dec_ref(x_21);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_189 = 1;
x_190 = lean_box(x_189);
lean_ctor_set(x_18, 0, x_190);
return x_18;
}
}
else
{
uint8_t x_191; lean_object* x_192; 
lean_dec_ref(x_20);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_191 = 1;
x_192 = lean_box(x_191);
lean_ctor_set(x_18, 0, x_192);
return x_18;
}
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_18, 0);
lean_inc(x_193);
lean_dec(x_18);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
lean_inc(x_8);
x_194 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_195 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_198; 
lean_dec(x_197);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_198 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_201; 
lean_dec(x_200);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_201 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_204; 
lean_dec(x_203);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_204 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_207; 
lean_dec(x_206);
x_207 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_209 = x_207;
} else {
 lean_dec_ref(x_207);
 x_209 = lean_box(0);
}
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; 
x_210 = 0;
x_211 = lean_box(x_210);
if (lean_is_scalar(x_209)) {
 x_212 = lean_alloc_ctor(0, 1, 0);
} else {
 x_212 = x_209;
}
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
else
{
uint8_t x_213; lean_object* x_214; lean_object* x_215; 
lean_dec_ref(x_208);
x_213 = 1;
x_214 = lean_box(x_213);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(0, 1, 0);
} else {
 x_215 = x_209;
}
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_207, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_217 = x_207;
} else {
 lean_dec_ref(x_207);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 1, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_216);
return x_218;
}
}
else
{
uint8_t x_219; lean_object* x_220; lean_object* x_221; 
lean_dec_ref(x_205);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_219 = 1;
x_220 = lean_box(x_219);
if (lean_is_scalar(x_206)) {
 x_221 = lean_alloc_ctor(0, 1, 0);
} else {
 x_221 = x_206;
}
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_222 = lean_ctor_get(x_204, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_223 = x_204;
} else {
 lean_dec_ref(x_204);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
else
{
uint8_t x_225; lean_object* x_226; lean_object* x_227; 
lean_dec_ref(x_202);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_225 = 1;
x_226 = lean_box(x_225);
if (lean_is_scalar(x_203)) {
 x_227 = lean_alloc_ctor(0, 1, 0);
} else {
 x_227 = x_203;
}
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_228 = lean_ctor_get(x_201, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_229 = x_201;
} else {
 lean_dec_ref(x_201);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
uint8_t x_231; lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_199);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_231 = 1;
x_232 = lean_box(x_231);
if (lean_is_scalar(x_200)) {
 x_233 = lean_alloc_ctor(0, 1, 0);
} else {
 x_233 = x_200;
}
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_234 = lean_ctor_get(x_198, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_235 = x_198;
} else {
 lean_dec_ref(x_198);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
else
{
uint8_t x_237; lean_object* x_238; lean_object* x_239; 
lean_dec_ref(x_196);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_237 = 1;
x_238 = lean_box(x_237);
if (lean_is_scalar(x_197)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_197;
}
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_240 = lean_ctor_get(x_195, 0);
lean_inc(x_240);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 x_241 = x_195;
} else {
 lean_dec_ref(x_195);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_240);
return x_242;
}
}
else
{
uint8_t x_243; lean_object* x_244; lean_object* x_245; 
lean_dec_ref(x_194);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_243 = 1;
x_244 = lean_box(x_243);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_244);
return x_245;
}
}
else
{
uint8_t x_246; lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_193);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_246 = 1;
x_247 = lean_box(x_246);
x_248 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_249 = !lean_is_exclusive(x_18);
if (x_249 == 0)
{
return x_18;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_18, 0);
lean_inc(x_250);
lean_dec(x_18);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; lean_object* x_253; 
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = 1;
x_253 = lean_box(x_252);
lean_ctor_set(x_15, 0, x_253);
return x_15;
}
}
else
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_15, 0);
lean_inc(x_254);
lean_dec(x_15);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_255 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_258; 
lean_inc(x_8);
x_258 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
lean_dec(x_257);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_259 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_262; 
lean_dec(x_261);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_262 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_264 = x_262;
} else {
 lean_dec_ref(x_262);
 x_264 = lean_box(0);
}
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_265; 
lean_dec(x_264);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_265 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_268; 
lean_dec(x_267);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_268 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_271; 
lean_dec(x_270);
x_271 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_274; lean_object* x_275; lean_object* x_276; 
x_274 = 0;
x_275 = lean_box(x_274);
if (lean_is_scalar(x_273)) {
 x_276 = lean_alloc_ctor(0, 1, 0);
} else {
 x_276 = x_273;
}
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
else
{
uint8_t x_277; lean_object* x_278; lean_object* x_279; 
lean_dec_ref(x_272);
x_277 = 1;
x_278 = lean_box(x_277);
if (lean_is_scalar(x_273)) {
 x_279 = lean_alloc_ctor(0, 1, 0);
} else {
 x_279 = x_273;
}
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_271, 0);
lean_inc(x_280);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 x_281 = x_271;
} else {
 lean_dec_ref(x_271);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_280);
return x_282;
}
}
else
{
uint8_t x_283; lean_object* x_284; lean_object* x_285; 
lean_dec_ref(x_269);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_283 = 1;
x_284 = lean_box(x_283);
if (lean_is_scalar(x_270)) {
 x_285 = lean_alloc_ctor(0, 1, 0);
} else {
 x_285 = x_270;
}
lean_ctor_set(x_285, 0, x_284);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_286 = lean_ctor_get(x_268, 0);
lean_inc(x_286);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 x_287 = x_268;
} else {
 lean_dec_ref(x_268);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 1, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_286);
return x_288;
}
}
else
{
uint8_t x_289; lean_object* x_290; lean_object* x_291; 
lean_dec_ref(x_266);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_289 = 1;
x_290 = lean_box(x_289);
if (lean_is_scalar(x_267)) {
 x_291 = lean_alloc_ctor(0, 1, 0);
} else {
 x_291 = x_267;
}
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_265, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 x_293 = x_265;
} else {
 lean_dec_ref(x_265);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_292);
return x_294;
}
}
else
{
uint8_t x_295; lean_object* x_296; lean_object* x_297; 
lean_dec_ref(x_263);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_295 = 1;
x_296 = lean_box(x_295);
if (lean_is_scalar(x_264)) {
 x_297 = lean_alloc_ctor(0, 1, 0);
} else {
 x_297 = x_264;
}
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_298 = lean_ctor_get(x_262, 0);
lean_inc(x_298);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 x_299 = x_262;
} else {
 lean_dec_ref(x_262);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 1, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_298);
return x_300;
}
}
else
{
uint8_t x_301; lean_object* x_302; lean_object* x_303; 
lean_dec_ref(x_260);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_301 = 1;
x_302 = lean_box(x_301);
if (lean_is_scalar(x_261)) {
 x_303 = lean_alloc_ctor(0, 1, 0);
} else {
 x_303 = x_261;
}
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_304 = lean_ctor_get(x_259, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 x_305 = x_259;
} else {
 lean_dec_ref(x_259);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_304);
return x_306;
}
}
else
{
uint8_t x_307; lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_258);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_307 = 1;
x_308 = lean_box(x_307);
if (lean_is_scalar(x_257)) {
 x_309 = lean_alloc_ctor(0, 1, 0);
} else {
 x_309 = x_257;
}
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
else
{
uint8_t x_310; lean_object* x_311; lean_object* x_312; 
lean_dec_ref(x_256);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_310 = 1;
x_311 = lean_box(x_310);
if (lean_is_scalar(x_257)) {
 x_312 = lean_alloc_ctor(0, 1, 0);
} else {
 x_312 = x_257;
}
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_313 = lean_ctor_get(x_255, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 x_314 = x_255;
} else {
 lean_dec_ref(x_255);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
return x_315;
}
}
else
{
uint8_t x_316; lean_object* x_317; lean_object* x_318; 
lean_dec_ref(x_254);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_316 = 1;
x_317 = lean_box(x_316);
x_318 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
}
}
else
{
uint8_t x_319; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_319 = !lean_is_exclusive(x_15);
if (x_319 == 0)
{
return x_15;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_15, 0);
lean_inc(x_320);
lean_dec(x_15);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
}
}
else
{
uint8_t x_322; lean_object* x_323; 
lean_dec_ref(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_322 = 1;
x_323 = lean_box(x_322);
lean_ctor_set(x_12, 0, x_323);
return x_12;
}
}
else
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_12, 0);
lean_inc(x_324);
lean_dec(x_12);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_325 = l_Lean_Meta_getFinValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_327 = x_325;
} else {
 lean_dec_ref(x_325);
 x_327 = lean_box(0);
}
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_328; 
lean_dec(x_327);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_328 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_330 = x_328;
} else {
 lean_dec_ref(x_328);
 x_330 = lean_box(0);
}
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_331; 
lean_inc(x_8);
x_331 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; 
lean_dec(x_330);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_332 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_334 = x_332;
} else {
 lean_dec_ref(x_332);
 x_334 = lean_box(0);
}
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_335; 
lean_dec(x_334);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_335 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_338; 
lean_dec(x_337);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_338 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_340 = x_338;
} else {
 lean_dec_ref(x_338);
 x_340 = lean_box(0);
}
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_341; 
lean_dec(x_340);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_341 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_344; 
lean_dec(x_343);
x_344 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_346 = x_344;
} else {
 lean_dec_ref(x_344);
 x_346 = lean_box(0);
}
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_347 = 0;
x_348 = lean_box(x_347);
if (lean_is_scalar(x_346)) {
 x_349 = lean_alloc_ctor(0, 1, 0);
} else {
 x_349 = x_346;
}
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
else
{
uint8_t x_350; lean_object* x_351; lean_object* x_352; 
lean_dec_ref(x_345);
x_350 = 1;
x_351 = lean_box(x_350);
if (lean_is_scalar(x_346)) {
 x_352 = lean_alloc_ctor(0, 1, 0);
} else {
 x_352 = x_346;
}
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_344, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_354 = x_344;
} else {
 lean_dec_ref(x_344);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
}
else
{
uint8_t x_356; lean_object* x_357; lean_object* x_358; 
lean_dec_ref(x_342);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_356 = 1;
x_357 = lean_box(x_356);
if (lean_is_scalar(x_343)) {
 x_358 = lean_alloc_ctor(0, 1, 0);
} else {
 x_358 = x_343;
}
lean_ctor_set(x_358, 0, x_357);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_359 = lean_ctor_get(x_341, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_360 = x_341;
} else {
 lean_dec_ref(x_341);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
return x_361;
}
}
else
{
uint8_t x_362; lean_object* x_363; lean_object* x_364; 
lean_dec_ref(x_339);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_362 = 1;
x_363 = lean_box(x_362);
if (lean_is_scalar(x_340)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_340;
}
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_365 = lean_ctor_get(x_338, 0);
lean_inc(x_365);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_366 = x_338;
} else {
 lean_dec_ref(x_338);
 x_366 = lean_box(0);
}
if (lean_is_scalar(x_366)) {
 x_367 = lean_alloc_ctor(1, 1, 0);
} else {
 x_367 = x_366;
}
lean_ctor_set(x_367, 0, x_365);
return x_367;
}
}
else
{
uint8_t x_368; lean_object* x_369; lean_object* x_370; 
lean_dec_ref(x_336);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_368 = 1;
x_369 = lean_box(x_368);
if (lean_is_scalar(x_337)) {
 x_370 = lean_alloc_ctor(0, 1, 0);
} else {
 x_370 = x_337;
}
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_371 = lean_ctor_get(x_335, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_372 = x_335;
} else {
 lean_dec_ref(x_335);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_371);
return x_373;
}
}
else
{
uint8_t x_374; lean_object* x_375; lean_object* x_376; 
lean_dec_ref(x_333);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_374 = 1;
x_375 = lean_box(x_374);
if (lean_is_scalar(x_334)) {
 x_376 = lean_alloc_ctor(0, 1, 0);
} else {
 x_376 = x_334;
}
lean_ctor_set(x_376, 0, x_375);
return x_376;
}
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_377 = lean_ctor_get(x_332, 0);
lean_inc(x_377);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_378 = x_332;
} else {
 lean_dec_ref(x_332);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_377);
return x_379;
}
}
else
{
uint8_t x_380; lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_331);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_380 = 1;
x_381 = lean_box(x_380);
if (lean_is_scalar(x_330)) {
 x_382 = lean_alloc_ctor(0, 1, 0);
} else {
 x_382 = x_330;
}
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
}
else
{
uint8_t x_383; lean_object* x_384; lean_object* x_385; 
lean_dec_ref(x_329);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_383 = 1;
x_384 = lean_box(x_383);
if (lean_is_scalar(x_330)) {
 x_385 = lean_alloc_ctor(0, 1, 0);
} else {
 x_385 = x_330;
}
lean_ctor_set(x_385, 0, x_384);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_386 = lean_ctor_get(x_328, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 x_387 = x_328;
} else {
 lean_dec_ref(x_328);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_386);
return x_388;
}
}
else
{
uint8_t x_389; lean_object* x_390; lean_object* x_391; 
lean_dec_ref(x_326);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_389 = 1;
x_390 = lean_box(x_389);
if (lean_is_scalar(x_327)) {
 x_391 = lean_alloc_ctor(0, 1, 0);
} else {
 x_391 = x_327;
}
lean_ctor_set(x_391, 0, x_390);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_392 = lean_ctor_get(x_325, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 x_393 = x_325;
} else {
 lean_dec_ref(x_325);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_392);
return x_394;
}
}
else
{
uint8_t x_395; lean_object* x_396; lean_object* x_397; 
lean_dec_ref(x_324);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_395 = 1;
x_396 = lean_box(x_395);
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
}
else
{
uint8_t x_398; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_398 = !lean_is_exclusive(x_12);
if (x_398 == 0)
{
return x_12;
}
else
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_12, 0);
lean_inc(x_399);
lean_dec(x_12);
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; lean_object* x_402; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_401 = 1;
x_402 = lean_box(x_401);
lean_ctor_set(x_9, 0, x_402);
return x_9;
}
}
else
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_9, 0);
lean_inc(x_403);
lean_dec(x_9);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_404 = l_Lean_Meta_getIntValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_406 = x_404;
} else {
 lean_dec_ref(x_404);
 x_406 = lean_box(0);
}
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_407; 
lean_dec(x_406);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_407 = l_Lean_Meta_getFinValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_409 = x_407;
} else {
 lean_dec_ref(x_407);
 x_409 = lean_box(0);
}
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_410; 
lean_dec(x_409);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_410 = l_Lean_Meta_getBitVecValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_412 = x_410;
} else {
 lean_dec_ref(x_410);
 x_412 = lean_box(0);
}
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_413; 
lean_inc(x_8);
x_413 = l_Lean_Meta_getStringValue_x3f(x_8);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
lean_dec(x_412);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_414 = l_Lean_Meta_getCharValue_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_417; 
lean_dec(x_416);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_417 = l_Lean_Meta_getUInt8Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 x_419 = x_417;
} else {
 lean_dec_ref(x_417);
 x_419 = lean_box(0);
}
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_420; 
lean_dec(x_419);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_420 = l_Lean_Meta_getUInt16Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_422 = x_420;
} else {
 lean_dec_ref(x_420);
 x_422 = lean_box(0);
}
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_423; 
lean_dec(x_422);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_423 = l_Lean_Meta_getUInt32Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_425 = x_423;
} else {
 lean_dec_ref(x_423);
 x_425 = lean_box(0);
}
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_426; 
lean_dec(x_425);
x_426 = l_Lean_Meta_getUInt64Value_x3f(x_8, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_428 = x_426;
} else {
 lean_dec_ref(x_426);
 x_428 = lean_box(0);
}
if (lean_obj_tag(x_427) == 0)
{
uint8_t x_429; lean_object* x_430; lean_object* x_431; 
x_429 = 0;
x_430 = lean_box(x_429);
if (lean_is_scalar(x_428)) {
 x_431 = lean_alloc_ctor(0, 1, 0);
} else {
 x_431 = x_428;
}
lean_ctor_set(x_431, 0, x_430);
return x_431;
}
else
{
uint8_t x_432; lean_object* x_433; lean_object* x_434; 
lean_dec_ref(x_427);
x_432 = 1;
x_433 = lean_box(x_432);
if (lean_is_scalar(x_428)) {
 x_434 = lean_alloc_ctor(0, 1, 0);
} else {
 x_434 = x_428;
}
lean_ctor_set(x_434, 0, x_433);
return x_434;
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_426, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_436 = x_426;
} else {
 lean_dec_ref(x_426);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_435);
return x_437;
}
}
else
{
uint8_t x_438; lean_object* x_439; lean_object* x_440; 
lean_dec_ref(x_424);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_438 = 1;
x_439 = lean_box(x_438);
if (lean_is_scalar(x_425)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_425;
}
lean_ctor_set(x_440, 0, x_439);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_441 = lean_ctor_get(x_423, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_442 = x_423;
} else {
 lean_dec_ref(x_423);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
}
else
{
uint8_t x_444; lean_object* x_445; lean_object* x_446; 
lean_dec_ref(x_421);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_444 = 1;
x_445 = lean_box(x_444);
if (lean_is_scalar(x_422)) {
 x_446 = lean_alloc_ctor(0, 1, 0);
} else {
 x_446 = x_422;
}
lean_ctor_set(x_446, 0, x_445);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_447 = lean_ctor_get(x_420, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 x_448 = x_420;
} else {
 lean_dec_ref(x_420);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_447);
return x_449;
}
}
else
{
uint8_t x_450; lean_object* x_451; lean_object* x_452; 
lean_dec_ref(x_418);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_450 = 1;
x_451 = lean_box(x_450);
if (lean_is_scalar(x_419)) {
 x_452 = lean_alloc_ctor(0, 1, 0);
} else {
 x_452 = x_419;
}
lean_ctor_set(x_452, 0, x_451);
return x_452;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_453 = lean_ctor_get(x_417, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 x_454 = x_417;
} else {
 lean_dec_ref(x_417);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
else
{
uint8_t x_456; lean_object* x_457; lean_object* x_458; 
lean_dec_ref(x_415);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_456 = 1;
x_457 = lean_box(x_456);
if (lean_is_scalar(x_416)) {
 x_458 = lean_alloc_ctor(0, 1, 0);
} else {
 x_458 = x_416;
}
lean_ctor_set(x_458, 0, x_457);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_459 = lean_ctor_get(x_414, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_460 = x_414;
} else {
 lean_dec_ref(x_414);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
else
{
uint8_t x_462; lean_object* x_463; lean_object* x_464; 
lean_dec_ref(x_413);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_462 = 1;
x_463 = lean_box(x_462);
if (lean_is_scalar(x_412)) {
 x_464 = lean_alloc_ctor(0, 1, 0);
} else {
 x_464 = x_412;
}
lean_ctor_set(x_464, 0, x_463);
return x_464;
}
}
else
{
uint8_t x_465; lean_object* x_466; lean_object* x_467; 
lean_dec_ref(x_411);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_465 = 1;
x_466 = lean_box(x_465);
if (lean_is_scalar(x_412)) {
 x_467 = lean_alloc_ctor(0, 1, 0);
} else {
 x_467 = x_412;
}
lean_ctor_set(x_467, 0, x_466);
return x_467;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_468 = lean_ctor_get(x_410, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_469 = x_410;
} else {
 lean_dec_ref(x_410);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 1, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_468);
return x_470;
}
}
else
{
uint8_t x_471; lean_object* x_472; lean_object* x_473; 
lean_dec_ref(x_408);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_471 = 1;
x_472 = lean_box(x_471);
if (lean_is_scalar(x_409)) {
 x_473 = lean_alloc_ctor(0, 1, 0);
} else {
 x_473 = x_409;
}
lean_ctor_set(x_473, 0, x_472);
return x_473;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_474 = lean_ctor_get(x_407, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 x_475 = x_407;
} else {
 lean_dec_ref(x_407);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 1, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_474);
return x_476;
}
}
else
{
uint8_t x_477; lean_object* x_478; lean_object* x_479; 
lean_dec_ref(x_405);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_477 = 1;
x_478 = lean_box(x_477);
if (lean_is_scalar(x_406)) {
 x_479 = lean_alloc_ctor(0, 1, 0);
} else {
 x_479 = x_406;
}
lean_ctor_set(x_479, 0, x_478);
return x_479;
}
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_480 = lean_ctor_get(x_404, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 x_481 = x_404;
} else {
 lean_dec_ref(x_404);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 1, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_480);
return x_482;
}
}
else
{
uint8_t x_483; lean_object* x_484; lean_object* x_485; 
lean_dec_ref(x_403);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_483 = 1;
x_484 = lean_box(x_483);
x_485 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_485, 0, x_484);
return x_485;
}
}
}
else
{
uint8_t x_486; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_486 = !lean_is_exclusive(x_9);
if (x_486 == 0)
{
return x_9;
}
else
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_9, 0);
lean_inc(x_487);
lean_dec(x_9);
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_487);
return x_488;
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
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
