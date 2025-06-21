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
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
x_16 = lean_ctor_get(x_14, 19);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 20);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_1);
x_18 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_17, x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_70; uint8_t x_71; 
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
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 x_51 = x_22;
} else {
 lean_dec_ref(x_22);
 x_51 = lean_box(0);
}
x_70 = lean_array_get_size(x_47);
x_71 = lean_nat_dec_lt(x_25, x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_dec(x_25);
x_52 = x_47;
goto block_69;
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_fget(x_47, x_25);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_72, 19);
x_75 = lean_ctor_get(x_72, 20);
x_76 = lean_box(0);
x_77 = lean_array_fset(x_47, x_25, x_76);
lean_inc(x_1);
x_78 = l_Lean_PersistentArray_push___redArg(x_74, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_79 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_75, x_1, x_24);
lean_ctor_set(x_72, 20, x_79);
lean_ctor_set(x_72, 19, x_78);
x_80 = lean_array_fset(x_77, x_25, x_72);
lean_dec(x_25);
x_52 = x_80;
goto block_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_81 = lean_ctor_get(x_72, 0);
x_82 = lean_ctor_get(x_72, 1);
x_83 = lean_ctor_get(x_72, 2);
x_84 = lean_ctor_get(x_72, 3);
x_85 = lean_ctor_get(x_72, 4);
x_86 = lean_ctor_get(x_72, 5);
x_87 = lean_ctor_get(x_72, 6);
x_88 = lean_ctor_get(x_72, 7);
x_89 = lean_ctor_get(x_72, 8);
x_90 = lean_ctor_get(x_72, 9);
x_91 = lean_ctor_get(x_72, 10);
x_92 = lean_ctor_get(x_72, 11);
x_93 = lean_ctor_get(x_72, 12);
x_94 = lean_ctor_get(x_72, 13);
x_95 = lean_ctor_get(x_72, 14);
x_96 = lean_ctor_get(x_72, 15);
x_97 = lean_ctor_get(x_72, 16);
x_98 = lean_ctor_get(x_72, 17);
x_99 = lean_ctor_get(x_72, 18);
x_100 = lean_ctor_get(x_72, 19);
x_101 = lean_ctor_get(x_72, 20);
x_102 = lean_ctor_get(x_72, 21);
x_103 = lean_ctor_get(x_72, 22);
x_104 = lean_ctor_get(x_72, 23);
x_105 = lean_ctor_get(x_72, 24);
x_106 = lean_ctor_get(x_72, 25);
x_107 = lean_ctor_get(x_72, 26);
x_108 = lean_ctor_get_uint8(x_72, sizeof(void*)*28);
x_109 = lean_ctor_get(x_72, 27);
lean_inc(x_109);
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
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_72);
x_110 = lean_box(0);
x_111 = lean_array_fset(x_47, x_25, x_110);
lean_inc(x_1);
x_112 = l_Lean_PersistentArray_push___redArg(x_100, x_1);
lean_inc(x_24);
lean_inc(x_1);
x_113 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_101, x_1, x_24);
x_114 = lean_alloc_ctor(0, 28, 1);
lean_ctor_set(x_114, 0, x_81);
lean_ctor_set(x_114, 1, x_82);
lean_ctor_set(x_114, 2, x_83);
lean_ctor_set(x_114, 3, x_84);
lean_ctor_set(x_114, 4, x_85);
lean_ctor_set(x_114, 5, x_86);
lean_ctor_set(x_114, 6, x_87);
lean_ctor_set(x_114, 7, x_88);
lean_ctor_set(x_114, 8, x_89);
lean_ctor_set(x_114, 9, x_90);
lean_ctor_set(x_114, 10, x_91);
lean_ctor_set(x_114, 11, x_92);
lean_ctor_set(x_114, 12, x_93);
lean_ctor_set(x_114, 13, x_94);
lean_ctor_set(x_114, 14, x_95);
lean_ctor_set(x_114, 15, x_96);
lean_ctor_set(x_114, 16, x_97);
lean_ctor_set(x_114, 17, x_98);
lean_ctor_set(x_114, 18, x_99);
lean_ctor_set(x_114, 19, x_112);
lean_ctor_set(x_114, 20, x_113);
lean_ctor_set(x_114, 21, x_102);
lean_ctor_set(x_114, 22, x_103);
lean_ctor_set(x_114, 23, x_104);
lean_ctor_set(x_114, 24, x_105);
lean_ctor_set(x_114, 25, x_106);
lean_ctor_set(x_114, 26, x_107);
lean_ctor_set(x_114, 27, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*28, x_108);
x_115 = lean_array_fset(x_111, x_25, x_114);
lean_dec(x_25);
x_52 = x_115;
goto block_69;
}
}
block_69:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 4, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
if (lean_is_scalar(x_46)) {
 x_54 = lean_alloc_ctor(0, 4, 0);
} else {
 x_54 = x_46;
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_44);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_45);
if (lean_is_scalar(x_42)) {
 x_55 = lean_alloc_ctor(0, 16, 1);
} else {
 x_55 = x_42;
}
lean_ctor_set(x_55, 0, x_26);
lean_ctor_set(x_55, 1, x_27);
lean_ctor_set(x_55, 2, x_28);
lean_ctor_set(x_55, 3, x_29);
lean_ctor_set(x_55, 4, x_30);
lean_ctor_set(x_55, 5, x_31);
lean_ctor_set(x_55, 6, x_32);
lean_ctor_set(x_55, 7, x_33);
lean_ctor_set(x_55, 8, x_35);
lean_ctor_set(x_55, 9, x_36);
lean_ctor_set(x_55, 10, x_37);
lean_ctor_set(x_55, 11, x_38);
lean_ctor_set(x_55, 12, x_39);
lean_ctor_set(x_55, 13, x_40);
lean_ctor_set(x_55, 14, x_54);
lean_ctor_set(x_55, 15, x_41);
lean_ctor_set_uint8(x_55, sizeof(void*)*16, x_34);
x_56 = lean_st_ref_set(x_3, x_55, x_23);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_inc(x_1);
x_58 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_24);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_24);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_116; 
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
x_116 = lean_ctor_get(x_18, 0);
lean_inc(x_116);
lean_dec(x_18);
lean_ctor_set(x_12, 0, x_116);
return x_12;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_12, 0);
x_118 = lean_ctor_get(x_12, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_12);
x_119 = lean_ctor_get(x_117, 19);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 20);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_1);
x_121 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_120, x_1);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_172; uint8_t x_173; 
x_122 = lean_st_ref_take(x_3, x_118);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 14);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 1);
lean_inc(x_126);
lean_dec(x_122);
x_127 = lean_ctor_get(x_119, 2);
lean_inc(x_127);
lean_dec(x_119);
x_128 = lean_ctor_get(x_2, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_123, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_123, 4);
lean_inc(x_133);
x_134 = lean_ctor_get(x_123, 5);
lean_inc(x_134);
x_135 = lean_ctor_get(x_123, 6);
lean_inc(x_135);
x_136 = lean_ctor_get(x_123, 7);
lean_inc(x_136);
x_137 = lean_ctor_get_uint8(x_123, sizeof(void*)*16);
x_138 = lean_ctor_get(x_123, 8);
lean_inc(x_138);
x_139 = lean_ctor_get(x_123, 9);
lean_inc(x_139);
x_140 = lean_ctor_get(x_123, 10);
lean_inc(x_140);
x_141 = lean_ctor_get(x_123, 11);
lean_inc(x_141);
x_142 = lean_ctor_get(x_123, 12);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 13);
lean_inc(x_143);
x_144 = lean_ctor_get(x_123, 15);
lean_inc(x_144);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 lean_ctor_release(x_123, 6);
 lean_ctor_release(x_123, 7);
 lean_ctor_release(x_123, 8);
 lean_ctor_release(x_123, 9);
 lean_ctor_release(x_123, 10);
 lean_ctor_release(x_123, 11);
 lean_ctor_release(x_123, 12);
 lean_ctor_release(x_123, 13);
 lean_ctor_release(x_123, 14);
 lean_ctor_release(x_123, 15);
 x_145 = x_123;
} else {
 lean_dec_ref(x_123);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_124, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_124, 1);
lean_inc(x_147);
x_148 = lean_ctor_get(x_124, 3);
lean_inc(x_148);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 x_149 = x_124;
} else {
 lean_dec_ref(x_124);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_125, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_125, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_125, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_125, 3);
lean_inc(x_153);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 x_154 = x_125;
} else {
 lean_dec_ref(x_125);
 x_154 = lean_box(0);
}
x_172 = lean_array_get_size(x_150);
x_173 = lean_nat_dec_lt(x_128, x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_dec(x_128);
x_155 = x_150;
goto block_171;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_174 = lean_array_fget(x_150, x_128);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_174, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_174, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_174, 4);
lean_inc(x_179);
x_180 = lean_ctor_get(x_174, 5);
lean_inc(x_180);
x_181 = lean_ctor_get(x_174, 6);
lean_inc(x_181);
x_182 = lean_ctor_get(x_174, 7);
lean_inc(x_182);
x_183 = lean_ctor_get(x_174, 8);
lean_inc(x_183);
x_184 = lean_ctor_get(x_174, 9);
lean_inc(x_184);
x_185 = lean_ctor_get(x_174, 10);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 11);
lean_inc(x_186);
x_187 = lean_ctor_get(x_174, 12);
lean_inc(x_187);
x_188 = lean_ctor_get(x_174, 13);
lean_inc(x_188);
x_189 = lean_ctor_get(x_174, 14);
lean_inc(x_189);
x_190 = lean_ctor_get(x_174, 15);
lean_inc(x_190);
x_191 = lean_ctor_get(x_174, 16);
lean_inc(x_191);
x_192 = lean_ctor_get(x_174, 17);
lean_inc(x_192);
x_193 = lean_ctor_get(x_174, 18);
lean_inc(x_193);
x_194 = lean_ctor_get(x_174, 19);
lean_inc(x_194);
x_195 = lean_ctor_get(x_174, 20);
lean_inc(x_195);
x_196 = lean_ctor_get(x_174, 21);
lean_inc(x_196);
x_197 = lean_ctor_get(x_174, 22);
lean_inc(x_197);
x_198 = lean_ctor_get(x_174, 23);
lean_inc(x_198);
x_199 = lean_ctor_get(x_174, 24);
lean_inc(x_199);
x_200 = lean_ctor_get(x_174, 25);
lean_inc(x_200);
x_201 = lean_ctor_get(x_174, 26);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_174, sizeof(void*)*28);
x_203 = lean_ctor_get(x_174, 27);
lean_inc(x_203);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 lean_ctor_release(x_174, 6);
 lean_ctor_release(x_174, 7);
 lean_ctor_release(x_174, 8);
 lean_ctor_release(x_174, 9);
 lean_ctor_release(x_174, 10);
 lean_ctor_release(x_174, 11);
 lean_ctor_release(x_174, 12);
 lean_ctor_release(x_174, 13);
 lean_ctor_release(x_174, 14);
 lean_ctor_release(x_174, 15);
 lean_ctor_release(x_174, 16);
 lean_ctor_release(x_174, 17);
 lean_ctor_release(x_174, 18);
 lean_ctor_release(x_174, 19);
 lean_ctor_release(x_174, 20);
 lean_ctor_release(x_174, 21);
 lean_ctor_release(x_174, 22);
 lean_ctor_release(x_174, 23);
 lean_ctor_release(x_174, 24);
 lean_ctor_release(x_174, 25);
 lean_ctor_release(x_174, 26);
 lean_ctor_release(x_174, 27);
 x_204 = x_174;
} else {
 lean_dec_ref(x_174);
 x_204 = lean_box(0);
}
x_205 = lean_box(0);
x_206 = lean_array_fset(x_150, x_128, x_205);
lean_inc(x_1);
x_207 = l_Lean_PersistentArray_push___redArg(x_194, x_1);
lean_inc(x_127);
lean_inc(x_1);
x_208 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_195, x_1, x_127);
if (lean_is_scalar(x_204)) {
 x_209 = lean_alloc_ctor(0, 28, 1);
} else {
 x_209 = x_204;
}
lean_ctor_set(x_209, 0, x_175);
lean_ctor_set(x_209, 1, x_176);
lean_ctor_set(x_209, 2, x_177);
lean_ctor_set(x_209, 3, x_178);
lean_ctor_set(x_209, 4, x_179);
lean_ctor_set(x_209, 5, x_180);
lean_ctor_set(x_209, 6, x_181);
lean_ctor_set(x_209, 7, x_182);
lean_ctor_set(x_209, 8, x_183);
lean_ctor_set(x_209, 9, x_184);
lean_ctor_set(x_209, 10, x_185);
lean_ctor_set(x_209, 11, x_186);
lean_ctor_set(x_209, 12, x_187);
lean_ctor_set(x_209, 13, x_188);
lean_ctor_set(x_209, 14, x_189);
lean_ctor_set(x_209, 15, x_190);
lean_ctor_set(x_209, 16, x_191);
lean_ctor_set(x_209, 17, x_192);
lean_ctor_set(x_209, 18, x_193);
lean_ctor_set(x_209, 19, x_207);
lean_ctor_set(x_209, 20, x_208);
lean_ctor_set(x_209, 21, x_196);
lean_ctor_set(x_209, 22, x_197);
lean_ctor_set(x_209, 23, x_198);
lean_ctor_set(x_209, 24, x_199);
lean_ctor_set(x_209, 25, x_200);
lean_ctor_set(x_209, 26, x_201);
lean_ctor_set(x_209, 27, x_203);
lean_ctor_set_uint8(x_209, sizeof(void*)*28, x_202);
x_210 = lean_array_fset(x_206, x_128, x_209);
lean_dec(x_128);
x_155 = x_210;
goto block_171;
}
block_171:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 4, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_151);
lean_ctor_set(x_156, 2, x_152);
lean_ctor_set(x_156, 3, x_153);
if (lean_is_scalar(x_149)) {
 x_157 = lean_alloc_ctor(0, 4, 0);
} else {
 x_157 = x_149;
}
lean_ctor_set(x_157, 0, x_146);
lean_ctor_set(x_157, 1, x_147);
lean_ctor_set(x_157, 2, x_156);
lean_ctor_set(x_157, 3, x_148);
if (lean_is_scalar(x_145)) {
 x_158 = lean_alloc_ctor(0, 16, 1);
} else {
 x_158 = x_145;
}
lean_ctor_set(x_158, 0, x_129);
lean_ctor_set(x_158, 1, x_130);
lean_ctor_set(x_158, 2, x_131);
lean_ctor_set(x_158, 3, x_132);
lean_ctor_set(x_158, 4, x_133);
lean_ctor_set(x_158, 5, x_134);
lean_ctor_set(x_158, 6, x_135);
lean_ctor_set(x_158, 7, x_136);
lean_ctor_set(x_158, 8, x_138);
lean_ctor_set(x_158, 9, x_139);
lean_ctor_set(x_158, 10, x_140);
lean_ctor_set(x_158, 11, x_141);
lean_ctor_set(x_158, 12, x_142);
lean_ctor_set(x_158, 13, x_143);
lean_ctor_set(x_158, 14, x_157);
lean_ctor_set(x_158, 15, x_144);
lean_ctor_set_uint8(x_158, sizeof(void*)*16, x_137);
x_159 = lean_st_ref_set(x_3, x_158, x_126);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
lean_inc(x_1);
x_161 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_127);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_127);
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_169 = x_163;
} else {
 lean_dec_ref(x_163);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_119);
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
x_211 = lean_ctor_get(x_121, 0);
lean_inc(x_211);
lean_dec(x_121);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_118);
return x_212;
}
}
}
else
{
uint8_t x_213; 
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
x_213 = !lean_is_exclusive(x_12);
if (x_213 == 0)
{
return x_12;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_12, 0);
x_215 = lean_ctor_get(x_12, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_12);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
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
