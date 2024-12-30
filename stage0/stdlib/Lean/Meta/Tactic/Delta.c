// Lean compiler output
// Module: Lean.Meta.Tactic.Delta
// Imports: Lean.Meta.Transform Lean.Meta.Tactic.Replace
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_deltaExpand___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_deltaTarget___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_deltaTarget___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_deltaExpand___closed__1;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_changeLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_change(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Environment_find_x3f(x_13, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_ConstantInfo_name(x_17);
x_19 = lean_apply_1(x_2, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
uint8_t x_22; 
x_22 = l_Lean_ConstantInfo_hasValue(x_17);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = l_Lean_ConstantInfo_levelParams(x_17);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_List_lengthTRAux___rarg(x_24, x_25);
lean_dec(x_24);
x_27 = l_List_lengthTRAux___rarg(x_8, x_25);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
else
{
lean_object* x_30; 
lean_free_object(x_9);
x_30 = l_Lean_Core_instantiateValueLevelParams(x_17, x_8, x_3, x_4, x_12);
lean_dec(x_17);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_25);
x_34 = lean_mk_empty_array_with_capacity(x_33);
lean_dec(x_33);
x_35 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_34);
x_36 = 1;
x_37 = 0;
x_38 = l_Lean_Expr_betaRev(x_32, x_35, x_36, x_37);
lean_dec(x_35);
lean_ctor_set(x_14, 0, x_38);
lean_ctor_set(x_30, 0, x_14);
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_25);
x_42 = lean_mk_empty_array_with_capacity(x_41);
lean_dec(x_41);
x_43 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_42);
x_44 = 1;
x_45 = 0;
x_46 = l_Lean_Expr_betaRev(x_39, x_43, x_44, x_45);
lean_dec(x_43);
lean_ctor_set(x_14, 0, x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_14);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_free_object(x_14);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_14, 0);
lean_inc(x_52);
lean_dec(x_14);
x_53 = l_Lean_ConstantInfo_name(x_52);
x_54 = lean_apply_1(x_2, x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_1);
x_56 = lean_box(0);
lean_ctor_set(x_9, 0, x_56);
return x_9;
}
else
{
uint8_t x_57; 
x_57 = l_Lean_ConstantInfo_hasValue(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_9, 0, x_58);
return x_9;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Lean_ConstantInfo_levelParams(x_52);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_List_lengthTRAux___rarg(x_59, x_60);
lean_dec(x_59);
x_62 = l_List_lengthTRAux___rarg(x_8, x_60);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec(x_1);
x_64 = lean_box(0);
lean_ctor_set(x_9, 0, x_64);
return x_9;
}
else
{
lean_object* x_65; 
lean_free_object(x_9);
x_65 = l_Lean_Core_instantiateValueLevelParams(x_52, x_8, x_3, x_4, x_12);
lean_dec(x_52);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_60);
x_70 = lean_mk_empty_array_with_capacity(x_69);
lean_dec(x_69);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_70);
x_72 = 1;
x_73 = 0;
x_74 = l_Lean_Expr_betaRev(x_66, x_71, x_72, x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_67);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_79 = x_65;
} else {
 lean_dec_ref(x_65);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_9, 0);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_9);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Environment_find_x3f(x_83, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_82);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_88 = x_84;
} else {
 lean_dec_ref(x_84);
 x_88 = lean_box(0);
}
x_89 = l_Lean_ConstantInfo_name(x_87);
x_90 = lean_apply_1(x_2, x_89);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = l_Lean_ConstantInfo_hasValue(x_87);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_1);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_82);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = l_Lean_ConstantInfo_levelParams(x_87);
x_98 = lean_unsigned_to_nat(0u);
x_99 = l_List_lengthTRAux___rarg(x_97, x_98);
lean_dec(x_97);
x_100 = l_List_lengthTRAux___rarg(x_8, x_98);
x_101 = lean_nat_dec_eq(x_99, x_100);
lean_dec(x_100);
lean_dec(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_82);
return x_103;
}
else
{
lean_object* x_104; 
x_104 = l_Lean_Core_instantiateValueLevelParams(x_87, x_8, x_3, x_4, x_82);
lean_dec(x_87);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_98);
x_109 = lean_mk_empty_array_with_capacity(x_108);
lean_dec(x_108);
x_110 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_1, x_109);
x_111 = 1;
x_112 = 0;
x_113 = l_Lean_Expr_betaRev(x_105, x_110, x_111, x_112);
lean_dec(x_110);
if (lean_is_scalar(x_88)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_88;
}
lean_ctor_set(x_114, 0, x_113);
if (lean_is_scalar(x_107)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_107;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_106);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_88);
lean_dec(x_1);
x_116 = lean_ctor_get(x_104, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_104, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_118 = x_104;
} else {
 lean_dec_ref(x_104);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_5);
return x_121;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_delta_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_delta_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_deltaExpand___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_delta_x3f(x_2, x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = l_Lean_Meta_deltaExpand___lambda__1___closed__1;
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_Lean_Meta_deltaExpand___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_6, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
return x_6;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_21 = x_7;
} else {
 lean_dec_ref(x_7);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_deltaExpand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_deltaExpand___lambda__1___boxed), 5, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_Meta_deltaExpand___closed__1;
x_8 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_deltaExpand___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_deltaExpand___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_deltaExpand___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_deltaExpand(x_12, x_3, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = l_Lean_MVarId_change(x_1, x_15, x_17, x_4, x_5, x_6, x_7, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_deltaTarget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("delta", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_deltaTarget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_deltaTarget___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_deltaTarget___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_deltaTarget___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
x_15 = l_Lean_Meta_deltaExpand(x_13, x_3, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l_Lean_MVarId_changeLocalDecl(x_1, x_4, x_16, x_18, x_5, x_6, x_7, x_8, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_deltaLocalDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_MVarId_deltaTarget___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_deltaLocalDecl___lambda__1), 9, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_2);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_deltaExpand___lambda__1___closed__1 = _init_l_Lean_Meta_deltaExpand___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_deltaExpand___lambda__1___closed__1);
l_Lean_Meta_deltaExpand___closed__1 = _init_l_Lean_Meta_deltaExpand___closed__1();
lean_mark_persistent(l_Lean_Meta_deltaExpand___closed__1);
l_Lean_MVarId_deltaTarget___closed__1 = _init_l_Lean_MVarId_deltaTarget___closed__1();
lean_mark_persistent(l_Lean_MVarId_deltaTarget___closed__1);
l_Lean_MVarId_deltaTarget___closed__2 = _init_l_Lean_MVarId_deltaTarget___closed__2();
lean_mark_persistent(l_Lean_MVarId_deltaTarget___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
