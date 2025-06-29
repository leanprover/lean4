// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: Lean.Meta.CtorRecognizer Lean.Meta.Tactic.Util Lean.Meta.Tactic.Clear
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
lean_object* l_Lean_Meta_isConstructorAppCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_73; lean_object* x_77; 
lean_inc(x_3);
lean_inc(x_1);
x_77 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_5, x_6, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_84; lean_object* x_121; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_121 = lean_ctor_get(x_78, 3);
lean_inc(x_121);
lean_dec(x_78);
x_84 = x_121;
goto block_120;
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
block_120:
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Expr_cleanupAnnotations(x_84);
x_86 = l_Lean_Expr_isApp(x_85);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_83;
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
x_88 = l_Lean_Expr_appFnCleanup___redArg(x_85);
x_89 = l_Lean_Expr_isApp(x_88);
if (x_89 == 0)
{
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_83;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
x_91 = l_Lean_Expr_appFnCleanup___redArg(x_88);
x_92 = l_Lean_Expr_isApp(x_91);
if (x_92 == 0)
{
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_83;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = l_Lean_Expr_appFnCleanup___redArg(x_91);
x_94 = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
x_95 = l_Lean_Expr_isConstOf(x_93, x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_83;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_80);
x_96 = l_Lean_Meta_isConstructorAppCore_x3f___redArg(x_90, x_6, x_79);
lean_dec(x_90);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Meta_isConstructorAppCore_x3f___redArg(x_87, x_6, x_98);
lean_dec(x_87);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_100; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_73 = x_100;
goto block_76;
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_73 = x_102;
goto block_76;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
lean_dec(x_97);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_101, 0);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_107 = !lean_is_exclusive(x_99);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_99, 1);
x_109 = lean_ctor_get(x_99, 0);
lean_dec(x_109);
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_name_eq(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
if (x_112 == 0)
{
if (x_95 == 0)
{
lean_free_object(x_99);
x_8 = x_108;
goto block_72;
}
else
{
lean_object* x_113; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = lean_box(0);
lean_ctor_set(x_99, 0, x_113);
return x_99;
}
}
else
{
lean_free_object(x_99);
x_8 = x_108;
goto block_72;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_ctor_get(x_99, 1);
lean_inc(x_114);
lean_dec(x_99);
x_115 = lean_ctor_get(x_104, 0);
lean_inc(x_115);
lean_dec(x_104);
x_116 = lean_ctor_get(x_106, 0);
lean_inc(x_116);
lean_dec(x_106);
x_117 = lean_name_eq(x_115, x_116);
lean_dec(x_116);
lean_dec(x_115);
if (x_117 == 0)
{
if (x_95 == 0)
{
x_8 = x_114;
goto block_72;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_114);
return x_119;
}
}
else
{
x_8 = x_114;
goto block_72;
}
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_77);
if (x_122 == 0)
{
return x_77;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_77, 0);
x_124 = lean_ctor_get(x_77, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_77);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
block_72:
{
lean_object* x_9; 
lean_inc(x_2);
x_9 = l_Lean_MVarId_getType(x_2, x_3, x_4, x_5, x_6, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_1);
x_12 = l_Lean_Expr_fvar___override(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Meta_mkNoConfusion(x_10, x_12, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
x_16 = lean_infer_type(x_14, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_Meta_whnfD(x_17, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
x_23 = l_Lean_MVarId_getTag(x_2, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_headBeta(x_22);
lean_inc(x_3);
x_27 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_26, x_24, x_3, x_4, x_5, x_6, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_Expr_app___override(x_14, x_28);
x_31 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_2, x_30, x_4, x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
x_34 = l_Lean_MVarId_clear(x_33, x_1, x_3, x_4, x_5, x_6, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_19, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_19, 0, x_52);
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
block_76:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_injection_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0 = _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0);
l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1 = _init_l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
