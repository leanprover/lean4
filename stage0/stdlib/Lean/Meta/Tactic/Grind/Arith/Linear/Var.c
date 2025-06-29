// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Var
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Util
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
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsLinarithTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_4 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 27);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 28);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_1);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_18, x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_73; uint8_t x_74; 
lean_free_object(x_13);
x_20 = lean_st_ref_take(x_4, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 14);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_17, 2);
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 7);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_21, sizeof(void*)*16);
x_35 = lean_ctor_get(x_21, 8);
lean_inc(x_35);
x_36 = lean_ctor_get(x_21, 9);
lean_inc(x_36);
x_37 = lean_ctor_get(x_21, 10);
lean_inc(x_37);
x_38 = lean_ctor_get(x_21, 11);
lean_inc(x_38);
x_39 = lean_ctor_get(x_21, 12);
lean_inc(x_39);
x_40 = lean_ctor_get(x_21, 13);
lean_inc(x_40);
x_41 = lean_ctor_get(x_21, 15);
lean_inc(x_41);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 lean_ctor_release(x_21, 4);
 lean_ctor_release(x_21, 5);
 lean_ctor_release(x_21, 6);
 lean_ctor_release(x_21, 7);
 lean_ctor_release(x_21, 8);
 lean_ctor_release(x_21, 9);
 lean_ctor_release(x_21, 10);
 lean_ctor_release(x_21, 11);
 lean_ctor_release(x_21, 12);
 lean_ctor_release(x_21, 13);
 lean_ctor_release(x_21, 14);
 lean_ctor_release(x_21, 15);
 x_42 = x_21;
} else {
 lean_dec_ref(x_21);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_22, 2);
lean_inc(x_45);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 x_46 = x_22;
} else {
 lean_dec_ref(x_22);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_23, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_23, 2);
lean_inc(x_49);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 x_50 = x_23;
} else {
 lean_dec_ref(x_23);
 x_50 = lean_box(0);
}
x_73 = lean_array_get_size(x_47);
x_74 = lean_nat_dec_lt(x_3, x_73);
lean_dec(x_73);
if (x_74 == 0)
{
x_51 = x_47;
goto block_72;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_array_fget(x_47, x_3);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_77 = lean_ctor_get(x_75, 27);
x_78 = lean_ctor_get(x_75, 28);
x_79 = lean_ctor_get(x_75, 29);
x_80 = lean_ctor_get(x_75, 30);
x_81 = lean_ctor_get(x_75, 31);
x_82 = lean_ctor_get(x_75, 35);
x_83 = lean_ctor_get(x_75, 37);
x_84 = lean_box(0);
x_85 = lean_array_fset(x_47, x_3, x_84);
lean_inc(x_1);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_1);
lean_inc(x_25);
lean_inc(x_1);
x_87 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_78, x_1, x_25);
x_88 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
x_89 = l_Lean_PersistentArray_push___redArg(x_79, x_88);
x_90 = l_Lean_PersistentArray_push___redArg(x_80, x_88);
x_91 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_92 = l_Lean_PersistentArray_push___redArg(x_81, x_91);
x_93 = lean_box(0);
x_94 = l_Lean_PersistentArray_push___redArg(x_82, x_93);
x_95 = lean_box(0);
x_96 = l_Lean_PersistentArray_push___redArg(x_83, x_95);
lean_ctor_set(x_75, 37, x_96);
lean_ctor_set(x_75, 35, x_94);
lean_ctor_set(x_75, 31, x_92);
lean_ctor_set(x_75, 30, x_90);
lean_ctor_set(x_75, 29, x_89);
lean_ctor_set(x_75, 28, x_87);
lean_ctor_set(x_75, 27, x_86);
x_97 = lean_array_fset(x_85, x_3, x_75);
x_51 = x_97;
goto block_72;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_98 = lean_ctor_get(x_75, 0);
x_99 = lean_ctor_get(x_75, 1);
x_100 = lean_ctor_get(x_75, 2);
x_101 = lean_ctor_get(x_75, 3);
x_102 = lean_ctor_get(x_75, 4);
x_103 = lean_ctor_get(x_75, 5);
x_104 = lean_ctor_get(x_75, 6);
x_105 = lean_ctor_get(x_75, 7);
x_106 = lean_ctor_get(x_75, 8);
x_107 = lean_ctor_get(x_75, 9);
x_108 = lean_ctor_get(x_75, 10);
x_109 = lean_ctor_get(x_75, 11);
x_110 = lean_ctor_get(x_75, 12);
x_111 = lean_ctor_get(x_75, 13);
x_112 = lean_ctor_get(x_75, 14);
x_113 = lean_ctor_get(x_75, 15);
x_114 = lean_ctor_get(x_75, 16);
x_115 = lean_ctor_get(x_75, 17);
x_116 = lean_ctor_get(x_75, 18);
x_117 = lean_ctor_get(x_75, 19);
x_118 = lean_ctor_get(x_75, 20);
x_119 = lean_ctor_get(x_75, 21);
x_120 = lean_ctor_get(x_75, 22);
x_121 = lean_ctor_get(x_75, 23);
x_122 = lean_ctor_get(x_75, 24);
x_123 = lean_ctor_get(x_75, 25);
x_124 = lean_ctor_get(x_75, 26);
x_125 = lean_ctor_get(x_75, 27);
x_126 = lean_ctor_get(x_75, 28);
x_127 = lean_ctor_get(x_75, 29);
x_128 = lean_ctor_get(x_75, 30);
x_129 = lean_ctor_get(x_75, 31);
x_130 = lean_ctor_get(x_75, 32);
x_131 = lean_ctor_get_uint8(x_75, sizeof(void*)*39);
x_132 = lean_ctor_get(x_75, 33);
x_133 = lean_ctor_get(x_75, 34);
x_134 = lean_ctor_get(x_75, 35);
x_135 = lean_ctor_get(x_75, 36);
x_136 = lean_ctor_get(x_75, 37);
x_137 = lean_ctor_get(x_75, 38);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
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
lean_dec(x_75);
x_138 = lean_box(0);
x_139 = lean_array_fset(x_47, x_3, x_138);
lean_inc(x_1);
x_140 = l_Lean_PersistentArray_push___redArg(x_125, x_1);
lean_inc(x_25);
lean_inc(x_1);
x_141 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_126, x_1, x_25);
x_142 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
x_143 = l_Lean_PersistentArray_push___redArg(x_127, x_142);
x_144 = l_Lean_PersistentArray_push___redArg(x_128, x_142);
x_145 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_146 = l_Lean_PersistentArray_push___redArg(x_129, x_145);
x_147 = lean_box(0);
x_148 = l_Lean_PersistentArray_push___redArg(x_134, x_147);
x_149 = lean_box(0);
x_150 = l_Lean_PersistentArray_push___redArg(x_136, x_149);
x_151 = lean_alloc_ctor(0, 39, 1);
lean_ctor_set(x_151, 0, x_98);
lean_ctor_set(x_151, 1, x_99);
lean_ctor_set(x_151, 2, x_100);
lean_ctor_set(x_151, 3, x_101);
lean_ctor_set(x_151, 4, x_102);
lean_ctor_set(x_151, 5, x_103);
lean_ctor_set(x_151, 6, x_104);
lean_ctor_set(x_151, 7, x_105);
lean_ctor_set(x_151, 8, x_106);
lean_ctor_set(x_151, 9, x_107);
lean_ctor_set(x_151, 10, x_108);
lean_ctor_set(x_151, 11, x_109);
lean_ctor_set(x_151, 12, x_110);
lean_ctor_set(x_151, 13, x_111);
lean_ctor_set(x_151, 14, x_112);
lean_ctor_set(x_151, 15, x_113);
lean_ctor_set(x_151, 16, x_114);
lean_ctor_set(x_151, 17, x_115);
lean_ctor_set(x_151, 18, x_116);
lean_ctor_set(x_151, 19, x_117);
lean_ctor_set(x_151, 20, x_118);
lean_ctor_set(x_151, 21, x_119);
lean_ctor_set(x_151, 22, x_120);
lean_ctor_set(x_151, 23, x_121);
lean_ctor_set(x_151, 24, x_122);
lean_ctor_set(x_151, 25, x_123);
lean_ctor_set(x_151, 26, x_124);
lean_ctor_set(x_151, 27, x_140);
lean_ctor_set(x_151, 28, x_141);
lean_ctor_set(x_151, 29, x_143);
lean_ctor_set(x_151, 30, x_144);
lean_ctor_set(x_151, 31, x_146);
lean_ctor_set(x_151, 32, x_130);
lean_ctor_set(x_151, 33, x_132);
lean_ctor_set(x_151, 34, x_133);
lean_ctor_set(x_151, 35, x_148);
lean_ctor_set(x_151, 36, x_135);
lean_ctor_set(x_151, 37, x_150);
lean_ctor_set(x_151, 38, x_137);
lean_ctor_set_uint8(x_151, sizeof(void*)*39, x_131);
x_152 = lean_array_fset(x_139, x_3, x_151);
x_51 = x_152;
goto block_72;
}
}
block_72:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 3, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_49);
if (lean_is_scalar(x_46)) {
 x_53 = lean_alloc_ctor(0, 4, 0);
} else {
 x_53 = x_46;
}
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_44);
lean_ctor_set(x_53, 2, x_45);
lean_ctor_set(x_53, 3, x_52);
if (lean_is_scalar(x_42)) {
 x_54 = lean_alloc_ctor(0, 16, 1);
} else {
 x_54 = x_42;
}
lean_ctor_set(x_54, 0, x_26);
lean_ctor_set(x_54, 1, x_27);
lean_ctor_set(x_54, 2, x_28);
lean_ctor_set(x_54, 3, x_29);
lean_ctor_set(x_54, 4, x_30);
lean_ctor_set(x_54, 5, x_31);
lean_ctor_set(x_54, 6, x_32);
lean_ctor_set(x_54, 7, x_33);
lean_ctor_set(x_54, 8, x_35);
lean_ctor_set(x_54, 9, x_36);
lean_ctor_set(x_54, 10, x_37);
lean_ctor_set(x_54, 11, x_38);
lean_ctor_set(x_54, 12, x_39);
lean_ctor_set(x_54, 13, x_40);
lean_ctor_set(x_54, 14, x_53);
lean_ctor_set(x_54, 15, x_41);
lean_ctor_set_uint8(x_54, sizeof(void*)*16, x_34);
x_55 = lean_st_ref_set(x_4, x_54, x_24);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_1);
x_57 = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_56);
if (x_2 == 0)
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_25);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_25);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = l_Lean_Meta_Grind_markAsLinarithTerm(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
lean_ctor_set(x_63, 0, x_25);
return x_63;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_25);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_25);
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
}
else
{
lean_object* x_153; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_19, 0);
lean_inc(x_153);
lean_dec(x_19);
lean_ctor_set(x_13, 0, x_153);
return x_13;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_13, 0);
x_155 = lean_ctor_get(x_13, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_13);
x_156 = lean_ctor_get(x_154, 27);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 28);
lean_inc(x_157);
lean_dec(x_154);
lean_inc(x_1);
x_158 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_157, x_1);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_210; uint8_t x_211; 
x_159 = lean_st_ref_take(x_4, x_155);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 14);
lean_inc(x_161);
x_162 = lean_ctor_get(x_161, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_164 = lean_ctor_get(x_156, 2);
lean_inc(x_164);
lean_dec(x_156);
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 3);
lean_inc(x_168);
x_169 = lean_ctor_get(x_160, 4);
lean_inc(x_169);
x_170 = lean_ctor_get(x_160, 5);
lean_inc(x_170);
x_171 = lean_ctor_get(x_160, 6);
lean_inc(x_171);
x_172 = lean_ctor_get(x_160, 7);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_160, sizeof(void*)*16);
x_174 = lean_ctor_get(x_160, 8);
lean_inc(x_174);
x_175 = lean_ctor_get(x_160, 9);
lean_inc(x_175);
x_176 = lean_ctor_get(x_160, 10);
lean_inc(x_176);
x_177 = lean_ctor_get(x_160, 11);
lean_inc(x_177);
x_178 = lean_ctor_get(x_160, 12);
lean_inc(x_178);
x_179 = lean_ctor_get(x_160, 13);
lean_inc(x_179);
x_180 = lean_ctor_get(x_160, 15);
lean_inc(x_180);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 lean_ctor_release(x_160, 6);
 lean_ctor_release(x_160, 7);
 lean_ctor_release(x_160, 8);
 lean_ctor_release(x_160, 9);
 lean_ctor_release(x_160, 10);
 lean_ctor_release(x_160, 11);
 lean_ctor_release(x_160, 12);
 lean_ctor_release(x_160, 13);
 lean_ctor_release(x_160, 14);
 lean_ctor_release(x_160, 15);
 x_181 = x_160;
} else {
 lean_dec_ref(x_160);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_161, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_161, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_161, 2);
lean_inc(x_184);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 lean_ctor_release(x_161, 2);
 lean_ctor_release(x_161, 3);
 x_185 = x_161;
} else {
 lean_dec_ref(x_161);
 x_185 = lean_box(0);
}
x_186 = lean_ctor_get(x_162, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_162, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_162, 2);
lean_inc(x_188);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_189 = x_162;
} else {
 lean_dec_ref(x_162);
 x_189 = lean_box(0);
}
x_210 = lean_array_get_size(x_186);
x_211 = lean_nat_dec_lt(x_3, x_210);
lean_dec(x_210);
if (x_211 == 0)
{
x_190 = x_186;
goto block_209;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_212 = lean_array_fget(x_186, x_3);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_212, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 3);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 4);
lean_inc(x_217);
x_218 = lean_ctor_get(x_212, 5);
lean_inc(x_218);
x_219 = lean_ctor_get(x_212, 6);
lean_inc(x_219);
x_220 = lean_ctor_get(x_212, 7);
lean_inc(x_220);
x_221 = lean_ctor_get(x_212, 8);
lean_inc(x_221);
x_222 = lean_ctor_get(x_212, 9);
lean_inc(x_222);
x_223 = lean_ctor_get(x_212, 10);
lean_inc(x_223);
x_224 = lean_ctor_get(x_212, 11);
lean_inc(x_224);
x_225 = lean_ctor_get(x_212, 12);
lean_inc(x_225);
x_226 = lean_ctor_get(x_212, 13);
lean_inc(x_226);
x_227 = lean_ctor_get(x_212, 14);
lean_inc(x_227);
x_228 = lean_ctor_get(x_212, 15);
lean_inc(x_228);
x_229 = lean_ctor_get(x_212, 16);
lean_inc(x_229);
x_230 = lean_ctor_get(x_212, 17);
lean_inc(x_230);
x_231 = lean_ctor_get(x_212, 18);
lean_inc(x_231);
x_232 = lean_ctor_get(x_212, 19);
lean_inc(x_232);
x_233 = lean_ctor_get(x_212, 20);
lean_inc(x_233);
x_234 = lean_ctor_get(x_212, 21);
lean_inc(x_234);
x_235 = lean_ctor_get(x_212, 22);
lean_inc(x_235);
x_236 = lean_ctor_get(x_212, 23);
lean_inc(x_236);
x_237 = lean_ctor_get(x_212, 24);
lean_inc(x_237);
x_238 = lean_ctor_get(x_212, 25);
lean_inc(x_238);
x_239 = lean_ctor_get(x_212, 26);
lean_inc(x_239);
x_240 = lean_ctor_get(x_212, 27);
lean_inc(x_240);
x_241 = lean_ctor_get(x_212, 28);
lean_inc(x_241);
x_242 = lean_ctor_get(x_212, 29);
lean_inc(x_242);
x_243 = lean_ctor_get(x_212, 30);
lean_inc(x_243);
x_244 = lean_ctor_get(x_212, 31);
lean_inc(x_244);
x_245 = lean_ctor_get(x_212, 32);
lean_inc(x_245);
x_246 = lean_ctor_get_uint8(x_212, sizeof(void*)*39);
x_247 = lean_ctor_get(x_212, 33);
lean_inc(x_247);
x_248 = lean_ctor_get(x_212, 34);
lean_inc(x_248);
x_249 = lean_ctor_get(x_212, 35);
lean_inc(x_249);
x_250 = lean_ctor_get(x_212, 36);
lean_inc(x_250);
x_251 = lean_ctor_get(x_212, 37);
lean_inc(x_251);
x_252 = lean_ctor_get(x_212, 38);
lean_inc(x_252);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 lean_ctor_release(x_212, 6);
 lean_ctor_release(x_212, 7);
 lean_ctor_release(x_212, 8);
 lean_ctor_release(x_212, 9);
 lean_ctor_release(x_212, 10);
 lean_ctor_release(x_212, 11);
 lean_ctor_release(x_212, 12);
 lean_ctor_release(x_212, 13);
 lean_ctor_release(x_212, 14);
 lean_ctor_release(x_212, 15);
 lean_ctor_release(x_212, 16);
 lean_ctor_release(x_212, 17);
 lean_ctor_release(x_212, 18);
 lean_ctor_release(x_212, 19);
 lean_ctor_release(x_212, 20);
 lean_ctor_release(x_212, 21);
 lean_ctor_release(x_212, 22);
 lean_ctor_release(x_212, 23);
 lean_ctor_release(x_212, 24);
 lean_ctor_release(x_212, 25);
 lean_ctor_release(x_212, 26);
 lean_ctor_release(x_212, 27);
 lean_ctor_release(x_212, 28);
 lean_ctor_release(x_212, 29);
 lean_ctor_release(x_212, 30);
 lean_ctor_release(x_212, 31);
 lean_ctor_release(x_212, 32);
 lean_ctor_release(x_212, 33);
 lean_ctor_release(x_212, 34);
 lean_ctor_release(x_212, 35);
 lean_ctor_release(x_212, 36);
 lean_ctor_release(x_212, 37);
 lean_ctor_release(x_212, 38);
 x_253 = x_212;
} else {
 lean_dec_ref(x_212);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
x_255 = lean_array_fset(x_186, x_3, x_254);
lean_inc(x_1);
x_256 = l_Lean_PersistentArray_push___redArg(x_240, x_1);
lean_inc(x_164);
lean_inc(x_1);
x_257 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_241, x_1, x_164);
x_258 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
x_259 = l_Lean_PersistentArray_push___redArg(x_242, x_258);
x_260 = l_Lean_PersistentArray_push___redArg(x_243, x_258);
x_261 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_262 = l_Lean_PersistentArray_push___redArg(x_244, x_261);
x_263 = lean_box(0);
x_264 = l_Lean_PersistentArray_push___redArg(x_249, x_263);
x_265 = lean_box(0);
x_266 = l_Lean_PersistentArray_push___redArg(x_251, x_265);
if (lean_is_scalar(x_253)) {
 x_267 = lean_alloc_ctor(0, 39, 1);
} else {
 x_267 = x_253;
}
lean_ctor_set(x_267, 0, x_213);
lean_ctor_set(x_267, 1, x_214);
lean_ctor_set(x_267, 2, x_215);
lean_ctor_set(x_267, 3, x_216);
lean_ctor_set(x_267, 4, x_217);
lean_ctor_set(x_267, 5, x_218);
lean_ctor_set(x_267, 6, x_219);
lean_ctor_set(x_267, 7, x_220);
lean_ctor_set(x_267, 8, x_221);
lean_ctor_set(x_267, 9, x_222);
lean_ctor_set(x_267, 10, x_223);
lean_ctor_set(x_267, 11, x_224);
lean_ctor_set(x_267, 12, x_225);
lean_ctor_set(x_267, 13, x_226);
lean_ctor_set(x_267, 14, x_227);
lean_ctor_set(x_267, 15, x_228);
lean_ctor_set(x_267, 16, x_229);
lean_ctor_set(x_267, 17, x_230);
lean_ctor_set(x_267, 18, x_231);
lean_ctor_set(x_267, 19, x_232);
lean_ctor_set(x_267, 20, x_233);
lean_ctor_set(x_267, 21, x_234);
lean_ctor_set(x_267, 22, x_235);
lean_ctor_set(x_267, 23, x_236);
lean_ctor_set(x_267, 24, x_237);
lean_ctor_set(x_267, 25, x_238);
lean_ctor_set(x_267, 26, x_239);
lean_ctor_set(x_267, 27, x_256);
lean_ctor_set(x_267, 28, x_257);
lean_ctor_set(x_267, 29, x_259);
lean_ctor_set(x_267, 30, x_260);
lean_ctor_set(x_267, 31, x_262);
lean_ctor_set(x_267, 32, x_245);
lean_ctor_set(x_267, 33, x_247);
lean_ctor_set(x_267, 34, x_248);
lean_ctor_set(x_267, 35, x_264);
lean_ctor_set(x_267, 36, x_250);
lean_ctor_set(x_267, 37, x_266);
lean_ctor_set(x_267, 38, x_252);
lean_ctor_set_uint8(x_267, sizeof(void*)*39, x_246);
x_268 = lean_array_fset(x_255, x_3, x_267);
x_190 = x_268;
goto block_209;
}
block_209:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
if (lean_is_scalar(x_189)) {
 x_191 = lean_alloc_ctor(0, 3, 0);
} else {
 x_191 = x_189;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
lean_ctor_set(x_191, 2, x_188);
if (lean_is_scalar(x_185)) {
 x_192 = lean_alloc_ctor(0, 4, 0);
} else {
 x_192 = x_185;
}
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_183);
lean_ctor_set(x_192, 2, x_184);
lean_ctor_set(x_192, 3, x_191);
if (lean_is_scalar(x_181)) {
 x_193 = lean_alloc_ctor(0, 16, 1);
} else {
 x_193 = x_181;
}
lean_ctor_set(x_193, 0, x_165);
lean_ctor_set(x_193, 1, x_166);
lean_ctor_set(x_193, 2, x_167);
lean_ctor_set(x_193, 3, x_168);
lean_ctor_set(x_193, 4, x_169);
lean_ctor_set(x_193, 5, x_170);
lean_ctor_set(x_193, 6, x_171);
lean_ctor_set(x_193, 7, x_172);
lean_ctor_set(x_193, 8, x_174);
lean_ctor_set(x_193, 9, x_175);
lean_ctor_set(x_193, 10, x_176);
lean_ctor_set(x_193, 11, x_177);
lean_ctor_set(x_193, 12, x_178);
lean_ctor_set(x_193, 13, x_179);
lean_ctor_set(x_193, 14, x_192);
lean_ctor_set(x_193, 15, x_180);
lean_ctor_set_uint8(x_193, sizeof(void*)*16, x_173);
x_194 = lean_st_ref_set(x_4, x_193, x_163);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
lean_inc(x_1);
x_196 = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_195);
if (x_2 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_164);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_dec(x_196);
x_201 = l_Lean_Meta_Grind_markAsLinarithTerm(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_164);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_164);
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_207 = x_201;
} else {
 lean_dec_ref(x_201);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_156);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_269 = lean_ctor_get(x_158, 0);
lean_inc(x_269);
lean_dec(x_158);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_155);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_13);
if (x_271 == 0)
{
return x_13;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_13, 0);
x_273 = lean_ctor_get(x_13, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_13);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Meta_Grind_Arith_Linear_mkVar(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
