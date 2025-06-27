// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Var
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.Util
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
lean_object* l_Lean_Meta_Grind_markAsCommRingTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 20);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 21);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_12);
x_19 = lean_st_ref_take(x_3, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 14);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_20, 7);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_20, sizeof(void*)*16);
x_35 = lean_ctor_get(x_20, 8);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 9);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 10);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 11);
lean_inc(x_38);
x_39 = lean_ctor_get(x_20, 12);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 13);
lean_inc(x_40);
x_41 = lean_ctor_get(x_20, 15);
lean_inc(x_41);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 lean_ctor_release(x_20, 9);
 lean_ctor_release(x_20, 10);
 lean_ctor_release(x_20, 11);
 lean_ctor_release(x_20, 12);
 lean_ctor_release(x_20, 13);
 lean_ctor_release(x_20, 14);
 lean_ctor_release(x_20, 15);
 x_42 = x_20;
} else {
 lean_dec_ref(x_20);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_21, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_21, 3);
lean_inc(x_45);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 x_46 = x_21;
} else {
 lean_dec_ref(x_21);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_22, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_22, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_22, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_22, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_22, 6);
lean_inc(x_53);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 lean_ctor_release(x_22, 6);
 x_54 = x_22;
} else {
 lean_dec_ref(x_22);
 x_54 = lean_box(0);
}
x_73 = lean_array_get_size(x_47);
x_74 = lean_nat_dec_lt(x_25, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_dec(x_25);
x_55 = x_47;
goto block_72;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_array_fget(x_47, x_25);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_75, 20);
x_78 = lean_ctor_get(x_75, 21);
x_79 = lean_box(0);
x_80 = lean_array_fset(x_47, x_25, x_79);
lean_inc(x_1);
x_81 = l_Lean_PersistentArray_push___redArg(x_77, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_82 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_78, x_1, x_24);
lean_ctor_set(x_75, 21, x_82);
lean_ctor_set(x_75, 20, x_81);
x_83 = lean_array_fset(x_80, x_25, x_75);
lean_dec(x_25);
x_55 = x_83;
goto block_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
x_86 = lean_ctor_get(x_75, 2);
x_87 = lean_ctor_get(x_75, 3);
x_88 = lean_ctor_get(x_75, 4);
x_89 = lean_ctor_get(x_75, 5);
x_90 = lean_ctor_get(x_75, 6);
x_91 = lean_ctor_get(x_75, 7);
x_92 = lean_ctor_get(x_75, 8);
x_93 = lean_ctor_get(x_75, 9);
x_94 = lean_ctor_get(x_75, 10);
x_95 = lean_ctor_get(x_75, 11);
x_96 = lean_ctor_get(x_75, 12);
x_97 = lean_ctor_get(x_75, 13);
x_98 = lean_ctor_get(x_75, 14);
x_99 = lean_ctor_get(x_75, 15);
x_100 = lean_ctor_get(x_75, 16);
x_101 = lean_ctor_get(x_75, 17);
x_102 = lean_ctor_get(x_75, 18);
x_103 = lean_ctor_get(x_75, 19);
x_104 = lean_ctor_get(x_75, 20);
x_105 = lean_ctor_get(x_75, 21);
x_106 = lean_ctor_get(x_75, 22);
x_107 = lean_ctor_get(x_75, 23);
x_108 = lean_ctor_get(x_75, 24);
x_109 = lean_ctor_get(x_75, 25);
x_110 = lean_ctor_get(x_75, 26);
x_111 = lean_ctor_get(x_75, 27);
x_112 = lean_ctor_get_uint8(x_75, sizeof(void*)*29);
x_113 = lean_ctor_get(x_75, 28);
lean_inc(x_113);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_114 = lean_box(0);
x_115 = lean_array_fset(x_47, x_25, x_114);
lean_inc(x_1);
x_116 = l_Lean_PersistentArray_push___redArg(x_104, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_117 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_105, x_1, x_24);
x_118 = lean_alloc_ctor(0, 29, 1);
lean_ctor_set(x_118, 0, x_84);
lean_ctor_set(x_118, 1, x_85);
lean_ctor_set(x_118, 2, x_86);
lean_ctor_set(x_118, 3, x_87);
lean_ctor_set(x_118, 4, x_88);
lean_ctor_set(x_118, 5, x_89);
lean_ctor_set(x_118, 6, x_90);
lean_ctor_set(x_118, 7, x_91);
lean_ctor_set(x_118, 8, x_92);
lean_ctor_set(x_118, 9, x_93);
lean_ctor_set(x_118, 10, x_94);
lean_ctor_set(x_118, 11, x_95);
lean_ctor_set(x_118, 12, x_96);
lean_ctor_set(x_118, 13, x_97);
lean_ctor_set(x_118, 14, x_98);
lean_ctor_set(x_118, 15, x_99);
lean_ctor_set(x_118, 16, x_100);
lean_ctor_set(x_118, 17, x_101);
lean_ctor_set(x_118, 18, x_102);
lean_ctor_set(x_118, 19, x_103);
lean_ctor_set(x_118, 20, x_116);
lean_ctor_set(x_118, 21, x_117);
lean_ctor_set(x_118, 22, x_106);
lean_ctor_set(x_118, 23, x_107);
lean_ctor_set(x_118, 24, x_108);
lean_ctor_set(x_118, 25, x_109);
lean_ctor_set(x_118, 26, x_110);
lean_ctor_set(x_118, 27, x_111);
lean_ctor_set(x_118, 28, x_113);
lean_ctor_set_uint8(x_118, sizeof(void*)*29, x_112);
x_119 = lean_array_fset(x_115, x_25, x_118);
lean_dec(x_25);
x_55 = x_119;
goto block_72;
}
}
block_72:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 7, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_49);
lean_ctor_set(x_56, 3, x_50);
lean_ctor_set(x_56, 4, x_51);
lean_ctor_set(x_56, 5, x_52);
lean_ctor_set(x_56, 6, x_53);
if (lean_is_scalar(x_46)) {
 x_57 = lean_alloc_ctor(0, 4, 0);
} else {
 x_57 = x_46;
}
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_45);
if (lean_is_scalar(x_42)) {
 x_58 = lean_alloc_ctor(0, 16, 1);
} else {
 x_58 = x_42;
}
lean_ctor_set(x_58, 0, x_26);
lean_ctor_set(x_58, 1, x_27);
lean_ctor_set(x_58, 2, x_28);
lean_ctor_set(x_58, 3, x_29);
lean_ctor_set(x_58, 4, x_30);
lean_ctor_set(x_58, 5, x_31);
lean_ctor_set(x_58, 6, x_32);
lean_ctor_set(x_58, 7, x_33);
lean_ctor_set(x_58, 8, x_35);
lean_ctor_set(x_58, 9, x_36);
lean_ctor_set(x_58, 10, x_37);
lean_ctor_set(x_58, 11, x_38);
lean_ctor_set(x_58, 12, x_39);
lean_ctor_set(x_58, 13, x_40);
lean_ctor_set(x_58, 14, x_57);
lean_ctor_set(x_58, 15, x_41);
lean_ctor_set_uint8(x_58, sizeof(void*)*16, x_34);
x_59 = lean_st_ref_set(x_3, x_58, x_23);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_inc(x_1);
x_61 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_24);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_24);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_24);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_18, 0);
lean_inc(x_120);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_120);
return x_12;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = lean_ctor_get(x_12, 0);
x_122 = lean_ctor_get(x_12, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_12);
x_123 = lean_ctor_get(x_121, 20);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 21);
lean_inc(x_124);
lean_dec(x_121);
lean_inc(x_1);
x_125 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_124, x_1);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_179; uint8_t x_180; 
x_126 = lean_st_ref_take(x_3, x_122);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 14);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_131 = lean_ctor_get(x_123, 2);
lean_inc(x_131);
lean_dec(x_123);
x_132 = lean_ctor_get(x_2, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_127, 4);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_127, 6);
lean_inc(x_139);
x_140 = lean_ctor_get(x_127, 7);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_127, sizeof(void*)*16);
x_142 = lean_ctor_get(x_127, 8);
lean_inc(x_142);
x_143 = lean_ctor_get(x_127, 9);
lean_inc(x_143);
x_144 = lean_ctor_get(x_127, 10);
lean_inc(x_144);
x_145 = lean_ctor_get(x_127, 11);
lean_inc(x_145);
x_146 = lean_ctor_get(x_127, 12);
lean_inc(x_146);
x_147 = lean_ctor_get(x_127, 13);
lean_inc(x_147);
x_148 = lean_ctor_get(x_127, 15);
lean_inc(x_148);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 lean_ctor_release(x_127, 4);
 lean_ctor_release(x_127, 5);
 lean_ctor_release(x_127, 6);
 lean_ctor_release(x_127, 7);
 lean_ctor_release(x_127, 8);
 lean_ctor_release(x_127, 9);
 lean_ctor_release(x_127, 10);
 lean_ctor_release(x_127, 11);
 lean_ctor_release(x_127, 12);
 lean_ctor_release(x_127, 13);
 lean_ctor_release(x_127, 14);
 lean_ctor_release(x_127, 15);
 x_149 = x_127;
} else {
 lean_dec_ref(x_127);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_128, 3);
lean_inc(x_152);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 x_153 = x_128;
} else {
 lean_dec_ref(x_128);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_129, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_129, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_129, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_129, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_129, 4);
lean_inc(x_158);
x_159 = lean_ctor_get(x_129, 5);
lean_inc(x_159);
x_160 = lean_ctor_get(x_129, 6);
lean_inc(x_160);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 lean_ctor_release(x_129, 5);
 lean_ctor_release(x_129, 6);
 x_161 = x_129;
} else {
 lean_dec_ref(x_129);
 x_161 = lean_box(0);
}
x_179 = lean_array_get_size(x_154);
x_180 = lean_nat_dec_lt(x_132, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_dec(x_132);
x_162 = x_154;
goto block_178;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_181 = lean_array_fget(x_154, x_132);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 3);
lean_inc(x_185);
x_186 = lean_ctor_get(x_181, 4);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 5);
lean_inc(x_187);
x_188 = lean_ctor_get(x_181, 6);
lean_inc(x_188);
x_189 = lean_ctor_get(x_181, 7);
lean_inc(x_189);
x_190 = lean_ctor_get(x_181, 8);
lean_inc(x_190);
x_191 = lean_ctor_get(x_181, 9);
lean_inc(x_191);
x_192 = lean_ctor_get(x_181, 10);
lean_inc(x_192);
x_193 = lean_ctor_get(x_181, 11);
lean_inc(x_193);
x_194 = lean_ctor_get(x_181, 12);
lean_inc(x_194);
x_195 = lean_ctor_get(x_181, 13);
lean_inc(x_195);
x_196 = lean_ctor_get(x_181, 14);
lean_inc(x_196);
x_197 = lean_ctor_get(x_181, 15);
lean_inc(x_197);
x_198 = lean_ctor_get(x_181, 16);
lean_inc(x_198);
x_199 = lean_ctor_get(x_181, 17);
lean_inc(x_199);
x_200 = lean_ctor_get(x_181, 18);
lean_inc(x_200);
x_201 = lean_ctor_get(x_181, 19);
lean_inc(x_201);
x_202 = lean_ctor_get(x_181, 20);
lean_inc(x_202);
x_203 = lean_ctor_get(x_181, 21);
lean_inc(x_203);
x_204 = lean_ctor_get(x_181, 22);
lean_inc(x_204);
x_205 = lean_ctor_get(x_181, 23);
lean_inc(x_205);
x_206 = lean_ctor_get(x_181, 24);
lean_inc(x_206);
x_207 = lean_ctor_get(x_181, 25);
lean_inc(x_207);
x_208 = lean_ctor_get(x_181, 26);
lean_inc(x_208);
x_209 = lean_ctor_get(x_181, 27);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_181, sizeof(void*)*29);
x_211 = lean_ctor_get(x_181, 28);
lean_inc(x_211);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 lean_ctor_release(x_181, 2);
 lean_ctor_release(x_181, 3);
 lean_ctor_release(x_181, 4);
 lean_ctor_release(x_181, 5);
 lean_ctor_release(x_181, 6);
 lean_ctor_release(x_181, 7);
 lean_ctor_release(x_181, 8);
 lean_ctor_release(x_181, 9);
 lean_ctor_release(x_181, 10);
 lean_ctor_release(x_181, 11);
 lean_ctor_release(x_181, 12);
 lean_ctor_release(x_181, 13);
 lean_ctor_release(x_181, 14);
 lean_ctor_release(x_181, 15);
 lean_ctor_release(x_181, 16);
 lean_ctor_release(x_181, 17);
 lean_ctor_release(x_181, 18);
 lean_ctor_release(x_181, 19);
 lean_ctor_release(x_181, 20);
 lean_ctor_release(x_181, 21);
 lean_ctor_release(x_181, 22);
 lean_ctor_release(x_181, 23);
 lean_ctor_release(x_181, 24);
 lean_ctor_release(x_181, 25);
 lean_ctor_release(x_181, 26);
 lean_ctor_release(x_181, 27);
 lean_ctor_release(x_181, 28);
 x_212 = x_181;
} else {
 lean_dec_ref(x_181);
 x_212 = lean_box(0);
}
x_213 = lean_box(0);
x_214 = lean_array_fset(x_154, x_132, x_213);
lean_inc(x_1);
x_215 = l_Lean_PersistentArray_push___redArg(x_202, x_1);
lean_inc(x_131);
lean_inc(x_1);
x_216 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_203, x_1, x_131);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 29, 1);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_182);
lean_ctor_set(x_217, 1, x_183);
lean_ctor_set(x_217, 2, x_184);
lean_ctor_set(x_217, 3, x_185);
lean_ctor_set(x_217, 4, x_186);
lean_ctor_set(x_217, 5, x_187);
lean_ctor_set(x_217, 6, x_188);
lean_ctor_set(x_217, 7, x_189);
lean_ctor_set(x_217, 8, x_190);
lean_ctor_set(x_217, 9, x_191);
lean_ctor_set(x_217, 10, x_192);
lean_ctor_set(x_217, 11, x_193);
lean_ctor_set(x_217, 12, x_194);
lean_ctor_set(x_217, 13, x_195);
lean_ctor_set(x_217, 14, x_196);
lean_ctor_set(x_217, 15, x_197);
lean_ctor_set(x_217, 16, x_198);
lean_ctor_set(x_217, 17, x_199);
lean_ctor_set(x_217, 18, x_200);
lean_ctor_set(x_217, 19, x_201);
lean_ctor_set(x_217, 20, x_215);
lean_ctor_set(x_217, 21, x_216);
lean_ctor_set(x_217, 22, x_204);
lean_ctor_set(x_217, 23, x_205);
lean_ctor_set(x_217, 24, x_206);
lean_ctor_set(x_217, 25, x_207);
lean_ctor_set(x_217, 26, x_208);
lean_ctor_set(x_217, 27, x_209);
lean_ctor_set(x_217, 28, x_211);
lean_ctor_set_uint8(x_217, sizeof(void*)*29, x_210);
x_218 = lean_array_fset(x_214, x_132, x_217);
lean_dec(x_132);
x_162 = x_218;
goto block_178;
}
block_178:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 7, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
lean_ctor_set(x_163, 4, x_158);
lean_ctor_set(x_163, 5, x_159);
lean_ctor_set(x_163, 6, x_160);
if (lean_is_scalar(x_153)) {
 x_164 = lean_alloc_ctor(0, 4, 0);
} else {
 x_164 = x_153;
}
lean_ctor_set(x_164, 0, x_150);
lean_ctor_set(x_164, 1, x_151);
lean_ctor_set(x_164, 2, x_163);
lean_ctor_set(x_164, 3, x_152);
if (lean_is_scalar(x_149)) {
 x_165 = lean_alloc_ctor(0, 16, 1);
} else {
 x_165 = x_149;
}
lean_ctor_set(x_165, 0, x_133);
lean_ctor_set(x_165, 1, x_134);
lean_ctor_set(x_165, 2, x_135);
lean_ctor_set(x_165, 3, x_136);
lean_ctor_set(x_165, 4, x_137);
lean_ctor_set(x_165, 5, x_138);
lean_ctor_set(x_165, 6, x_139);
lean_ctor_set(x_165, 7, x_140);
lean_ctor_set(x_165, 8, x_142);
lean_ctor_set(x_165, 9, x_143);
lean_ctor_set(x_165, 10, x_144);
lean_ctor_set(x_165, 11, x_145);
lean_ctor_set(x_165, 12, x_146);
lean_ctor_set(x_165, 13, x_147);
lean_ctor_set(x_165, 14, x_164);
lean_ctor_set(x_165, 15, x_148);
lean_ctor_set_uint8(x_165, sizeof(void*)*16, x_141);
x_166 = lean_st_ref_set(x_3, x_165, x_130);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
lean_inc(x_1);
x_168 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_167);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_131);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_131);
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_176 = x_170;
} else {
 lean_dec_ref(x_170);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_123);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_219 = lean_ctor_get(x_125, 0);
lean_inc(x_219);
lean_dec(x_125);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_122);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_12);
if (x_221 == 0)
{
return x_12;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_12, 0);
x_223 = lean_ctor_get(x_12, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_12);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_getSemiring(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 13);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 14);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_72; uint8_t x_73; 
lean_free_object(x_12);
x_19 = lean_st_ref_take(x_3, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 14);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_20, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_20, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_20, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_20, 7);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_20, sizeof(void*)*16);
x_34 = lean_ctor_get(x_20, 8);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 10);
lean_inc(x_36);
x_37 = lean_ctor_get(x_20, 11);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 12);
lean_inc(x_38);
x_39 = lean_ctor_get(x_20, 13);
lean_inc(x_39);
x_40 = lean_ctor_get(x_20, 15);
lean_inc(x_40);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 lean_ctor_release(x_20, 9);
 lean_ctor_release(x_20, 10);
 lean_ctor_release(x_20, 11);
 lean_ctor_release(x_20, 12);
 lean_ctor_release(x_20, 13);
 lean_ctor_release(x_20, 14);
 lean_ctor_release(x_20, 15);
 x_41 = x_20;
} else {
 lean_dec_ref(x_20);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_21, 3);
lean_inc(x_44);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 x_45 = x_21;
} else {
 lean_dec_ref(x_21);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_22, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_22, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_22, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_22, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_22, 6);
lean_inc(x_52);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 lean_ctor_release(x_22, 6);
 x_53 = x_22;
} else {
 lean_dec_ref(x_22);
 x_53 = lean_box(0);
}
x_72 = lean_array_get_size(x_49);
x_73 = lean_nat_dec_lt(x_2, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
x_54 = x_49;
goto block_71;
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_array_fget(x_49, x_2);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_74, 13);
x_77 = lean_ctor_get(x_74, 14);
x_78 = lean_box(0);
x_79 = lean_array_fset(x_49, x_2, x_78);
lean_inc(x_1);
x_80 = l_Lean_PersistentArray_push___redArg(x_76, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_81 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_77, x_1, x_24);
lean_ctor_set(x_74, 14, x_81);
lean_ctor_set(x_74, 13, x_80);
x_82 = lean_array_fset(x_79, x_2, x_74);
x_54 = x_82;
goto block_71;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
x_85 = lean_ctor_get(x_74, 2);
x_86 = lean_ctor_get(x_74, 3);
x_87 = lean_ctor_get(x_74, 4);
x_88 = lean_ctor_get(x_74, 5);
x_89 = lean_ctor_get(x_74, 6);
x_90 = lean_ctor_get(x_74, 7);
x_91 = lean_ctor_get(x_74, 8);
x_92 = lean_ctor_get(x_74, 9);
x_93 = lean_ctor_get(x_74, 10);
x_94 = lean_ctor_get(x_74, 11);
x_95 = lean_ctor_get(x_74, 12);
x_96 = lean_ctor_get(x_74, 13);
x_97 = lean_ctor_get(x_74, 14);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_98 = lean_box(0);
x_99 = lean_array_fset(x_49, x_2, x_98);
lean_inc(x_1);
x_100 = l_Lean_PersistentArray_push___redArg(x_96, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_101 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_97, x_1, x_24);
x_102 = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(x_102, 0, x_83);
lean_ctor_set(x_102, 1, x_84);
lean_ctor_set(x_102, 2, x_85);
lean_ctor_set(x_102, 3, x_86);
lean_ctor_set(x_102, 4, x_87);
lean_ctor_set(x_102, 5, x_88);
lean_ctor_set(x_102, 6, x_89);
lean_ctor_set(x_102, 7, x_90);
lean_ctor_set(x_102, 8, x_91);
lean_ctor_set(x_102, 9, x_92);
lean_ctor_set(x_102, 10, x_93);
lean_ctor_set(x_102, 11, x_94);
lean_ctor_set(x_102, 12, x_95);
lean_ctor_set(x_102, 13, x_100);
lean_ctor_set(x_102, 14, x_101);
x_103 = lean_array_fset(x_99, x_2, x_102);
x_54 = x_103;
goto block_71;
}
}
block_71:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 7, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_47);
lean_ctor_set(x_55, 2, x_48);
lean_ctor_set(x_55, 3, x_54);
lean_ctor_set(x_55, 4, x_50);
lean_ctor_set(x_55, 5, x_51);
lean_ctor_set(x_55, 6, x_52);
if (lean_is_scalar(x_45)) {
 x_56 = lean_alloc_ctor(0, 4, 0);
} else {
 x_56 = x_45;
}
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_43);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_44);
if (lean_is_scalar(x_41)) {
 x_57 = lean_alloc_ctor(0, 16, 1);
} else {
 x_57 = x_41;
}
lean_ctor_set(x_57, 0, x_25);
lean_ctor_set(x_57, 1, x_26);
lean_ctor_set(x_57, 2, x_27);
lean_ctor_set(x_57, 3, x_28);
lean_ctor_set(x_57, 4, x_29);
lean_ctor_set(x_57, 5, x_30);
lean_ctor_set(x_57, 6, x_31);
lean_ctor_set(x_57, 7, x_32);
lean_ctor_set(x_57, 8, x_34);
lean_ctor_set(x_57, 9, x_35);
lean_ctor_set(x_57, 10, x_36);
lean_ctor_set(x_57, 11, x_37);
lean_ctor_set(x_57, 12, x_38);
lean_ctor_set(x_57, 13, x_39);
lean_ctor_set(x_57, 14, x_56);
lean_ctor_set(x_57, 15, x_40);
lean_ctor_set_uint8(x_57, sizeof(void*)*16, x_33);
x_58 = lean_st_ref_set(x_3, x_57, x_23);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
lean_inc(x_1);
x_60 = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_62, 0, x_24);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_24);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_24);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_18, 0);
lean_inc(x_104);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_104);
return x_12;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_12, 0);
x_106 = lean_ctor_get(x_12, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_12);
x_107 = lean_ctor_get(x_105, 13);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 14);
lean_inc(x_108);
lean_dec(x_105);
lean_inc(x_1);
x_109 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_108, x_1);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_162; uint8_t x_163; 
x_110 = lean_st_ref_take(x_3, x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 14);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = lean_ctor_get(x_107, 2);
lean_inc(x_115);
lean_dec(x_107);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_111, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_111, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_111, 5);
lean_inc(x_121);
x_122 = lean_ctor_get(x_111, 6);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 7);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_111, sizeof(void*)*16);
x_125 = lean_ctor_get(x_111, 8);
lean_inc(x_125);
x_126 = lean_ctor_get(x_111, 9);
lean_inc(x_126);
x_127 = lean_ctor_get(x_111, 10);
lean_inc(x_127);
x_128 = lean_ctor_get(x_111, 11);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 12);
lean_inc(x_129);
x_130 = lean_ctor_get(x_111, 13);
lean_inc(x_130);
x_131 = lean_ctor_get(x_111, 15);
lean_inc(x_131);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 lean_ctor_release(x_111, 5);
 lean_ctor_release(x_111, 6);
 lean_ctor_release(x_111, 7);
 lean_ctor_release(x_111, 8);
 lean_ctor_release(x_111, 9);
 lean_ctor_release(x_111, 10);
 lean_ctor_release(x_111, 11);
 lean_ctor_release(x_111, 12);
 lean_ctor_release(x_111, 13);
 lean_ctor_release(x_111, 14);
 lean_ctor_release(x_111, 15);
 x_132 = x_111;
} else {
 lean_dec_ref(x_111);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_112, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_112, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_112, 3);
lean_inc(x_135);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 lean_ctor_release(x_112, 3);
 x_136 = x_112;
} else {
 lean_dec_ref(x_112);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_113, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_113, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_113, 2);
lean_inc(x_139);
x_140 = lean_ctor_get(x_113, 3);
lean_inc(x_140);
x_141 = lean_ctor_get(x_113, 4);
lean_inc(x_141);
x_142 = lean_ctor_get(x_113, 5);
lean_inc(x_142);
x_143 = lean_ctor_get(x_113, 6);
lean_inc(x_143);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 lean_ctor_release(x_113, 2);
 lean_ctor_release(x_113, 3);
 lean_ctor_release(x_113, 4);
 lean_ctor_release(x_113, 5);
 lean_ctor_release(x_113, 6);
 x_144 = x_113;
} else {
 lean_dec_ref(x_113);
 x_144 = lean_box(0);
}
x_162 = lean_array_get_size(x_140);
x_163 = lean_nat_dec_lt(x_2, x_162);
lean_dec(x_162);
if (x_163 == 0)
{
x_145 = x_140;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_164 = lean_array_fget(x_140, x_2);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_164, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_164, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_164, 5);
lean_inc(x_170);
x_171 = lean_ctor_get(x_164, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_164, 7);
lean_inc(x_172);
x_173 = lean_ctor_get(x_164, 8);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 9);
lean_inc(x_174);
x_175 = lean_ctor_get(x_164, 10);
lean_inc(x_175);
x_176 = lean_ctor_get(x_164, 11);
lean_inc(x_176);
x_177 = lean_ctor_get(x_164, 12);
lean_inc(x_177);
x_178 = lean_ctor_get(x_164, 13);
lean_inc(x_178);
x_179 = lean_ctor_get(x_164, 14);
lean_inc(x_179);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 lean_ctor_release(x_164, 3);
 lean_ctor_release(x_164, 4);
 lean_ctor_release(x_164, 5);
 lean_ctor_release(x_164, 6);
 lean_ctor_release(x_164, 7);
 lean_ctor_release(x_164, 8);
 lean_ctor_release(x_164, 9);
 lean_ctor_release(x_164, 10);
 lean_ctor_release(x_164, 11);
 lean_ctor_release(x_164, 12);
 lean_ctor_release(x_164, 13);
 lean_ctor_release(x_164, 14);
 x_180 = x_164;
} else {
 lean_dec_ref(x_164);
 x_180 = lean_box(0);
}
x_181 = lean_box(0);
x_182 = lean_array_fset(x_140, x_2, x_181);
lean_inc(x_1);
x_183 = l_Lean_PersistentArray_push___redArg(x_178, x_1);
lean_inc(x_115);
lean_inc(x_1);
x_184 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_179, x_1, x_115);
if (lean_is_scalar(x_180)) {
 x_185 = lean_alloc_ctor(0, 15, 0);
} else {
 x_185 = x_180;
}
lean_ctor_set(x_185, 0, x_165);
lean_ctor_set(x_185, 1, x_166);
lean_ctor_set(x_185, 2, x_167);
lean_ctor_set(x_185, 3, x_168);
lean_ctor_set(x_185, 4, x_169);
lean_ctor_set(x_185, 5, x_170);
lean_ctor_set(x_185, 6, x_171);
lean_ctor_set(x_185, 7, x_172);
lean_ctor_set(x_185, 8, x_173);
lean_ctor_set(x_185, 9, x_174);
lean_ctor_set(x_185, 10, x_175);
lean_ctor_set(x_185, 11, x_176);
lean_ctor_set(x_185, 12, x_177);
lean_ctor_set(x_185, 13, x_183);
lean_ctor_set(x_185, 14, x_184);
x_186 = lean_array_fset(x_182, x_2, x_185);
x_145 = x_186;
goto block_161;
}
block_161:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 7, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set(x_146, 1, x_138);
lean_ctor_set(x_146, 2, x_139);
lean_ctor_set(x_146, 3, x_145);
lean_ctor_set(x_146, 4, x_141);
lean_ctor_set(x_146, 5, x_142);
lean_ctor_set(x_146, 6, x_143);
if (lean_is_scalar(x_136)) {
 x_147 = lean_alloc_ctor(0, 4, 0);
} else {
 x_147 = x_136;
}
lean_ctor_set(x_147, 0, x_133);
lean_ctor_set(x_147, 1, x_134);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_135);
if (lean_is_scalar(x_132)) {
 x_148 = lean_alloc_ctor(0, 16, 1);
} else {
 x_148 = x_132;
}
lean_ctor_set(x_148, 0, x_116);
lean_ctor_set(x_148, 1, x_117);
lean_ctor_set(x_148, 2, x_118);
lean_ctor_set(x_148, 3, x_119);
lean_ctor_set(x_148, 4, x_120);
lean_ctor_set(x_148, 5, x_121);
lean_ctor_set(x_148, 6, x_122);
lean_ctor_set(x_148, 7, x_123);
lean_ctor_set(x_148, 8, x_125);
lean_ctor_set(x_148, 9, x_126);
lean_ctor_set(x_148, 10, x_127);
lean_ctor_set(x_148, 11, x_128);
lean_ctor_set(x_148, 12, x_129);
lean_ctor_set(x_148, 13, x_130);
lean_ctor_set(x_148, 14, x_147);
lean_ctor_set(x_148, 15, x_131);
lean_ctor_set_uint8(x_148, sizeof(void*)*16, x_124);
x_149 = lean_st_ref_set(x_3, x_148, x_114);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
lean_inc(x_1);
x_151 = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_115);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_115);
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_159 = x_153;
} else {
 lean_dec_ref(x_153);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_107);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_109, 0);
lean_inc(x_187);
lean_dec(x_109);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_106);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_12);
if (x_189 == 0)
{
return x_12;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_12, 0);
x_191 = lean_ctor_get(x_12, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_12);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
