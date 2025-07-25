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
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1;
lean_object* l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsLinarithTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
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
x_3 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5;
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 28);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_15, 29);
lean_inc_ref(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_20 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1;
lean_inc_ref(x_1);
x_21 = l_Lean_PersistentHashMap_find_x3f___redArg(x_19, x_20, x_18, x_1);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_75; uint8_t x_76; 
lean_free_object(x_13);
x_22 = lean_st_ref_take(x_4, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 14);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec_ref(x_22);
x_27 = lean_ctor_get(x_17, 2);
lean_inc(x_27);
lean_dec_ref(x_17);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_23, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_23, 4);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_23, 5);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_23, 6);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_23, 7);
lean_inc_ref(x_35);
x_36 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_37 = lean_ctor_get(x_23, 8);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 9);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_23, 10);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_23, 11);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_23, 12);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_23, 13);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_23, 15);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 lean_ctor_release(x_23, 4);
 lean_ctor_release(x_23, 5);
 lean_ctor_release(x_23, 6);
 lean_ctor_release(x_23, 7);
 lean_ctor_release(x_23, 8);
 lean_ctor_release(x_23, 9);
 lean_ctor_release(x_23, 10);
 lean_ctor_release(x_23, 11);
 lean_ctor_release(x_23, 12);
 lean_ctor_release(x_23, 13);
 lean_ctor_release(x_23, 14);
 lean_ctor_release(x_23, 15);
 x_44 = x_23;
} else {
 lean_dec_ref(x_23);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_47);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 x_48 = x_24;
} else {
 lean_dec_ref(x_24);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_25, 2);
lean_inc_ref(x_51);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 x_52 = x_25;
} else {
 lean_dec_ref(x_25);
 x_52 = lean_box(0);
}
x_75 = lean_array_get_size(x_49);
x_76 = lean_nat_dec_lt(x_3, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
x_53 = x_49;
goto block_74;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_array_fget(x_49, x_3);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_79 = lean_ctor_get(x_77, 28);
x_80 = lean_ctor_get(x_77, 29);
x_81 = lean_ctor_get(x_77, 30);
x_82 = lean_ctor_get(x_77, 31);
x_83 = lean_ctor_get(x_77, 32);
x_84 = lean_ctor_get(x_77, 36);
x_85 = lean_ctor_get(x_77, 38);
x_86 = lean_box(0);
x_87 = lean_array_fset(x_49, x_3, x_86);
lean_inc_ref(x_1);
x_88 = l_Lean_PersistentArray_push___redArg(x_79, x_1);
lean_inc(x_27);
lean_inc_ref(x_1);
x_89 = l_Lean_PersistentHashMap_insert___redArg(x_19, x_20, x_80, x_1, x_27);
x_90 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_91 = l_Lean_PersistentArray_push___redArg(x_81, x_90);
x_92 = l_Lean_PersistentArray_push___redArg(x_82, x_90);
x_93 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6;
x_94 = l_Lean_PersistentArray_push___redArg(x_83, x_93);
x_95 = lean_box(0);
x_96 = l_Lean_PersistentArray_push___redArg(x_84, x_95);
x_97 = lean_box(1);
x_98 = l_Lean_PersistentArray_push___redArg(x_85, x_97);
lean_ctor_set(x_77, 38, x_98);
lean_ctor_set(x_77, 36, x_96);
lean_ctor_set(x_77, 32, x_94);
lean_ctor_set(x_77, 31, x_92);
lean_ctor_set(x_77, 30, x_91);
lean_ctor_set(x_77, 29, x_89);
lean_ctor_set(x_77, 28, x_88);
x_99 = lean_array_fset(x_87, x_3, x_77);
x_53 = x_99;
goto block_74;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_100 = lean_ctor_get(x_77, 0);
x_101 = lean_ctor_get(x_77, 1);
x_102 = lean_ctor_get(x_77, 2);
x_103 = lean_ctor_get(x_77, 3);
x_104 = lean_ctor_get(x_77, 4);
x_105 = lean_ctor_get(x_77, 5);
x_106 = lean_ctor_get(x_77, 6);
x_107 = lean_ctor_get(x_77, 7);
x_108 = lean_ctor_get(x_77, 8);
x_109 = lean_ctor_get(x_77, 9);
x_110 = lean_ctor_get(x_77, 10);
x_111 = lean_ctor_get(x_77, 11);
x_112 = lean_ctor_get(x_77, 12);
x_113 = lean_ctor_get(x_77, 13);
x_114 = lean_ctor_get(x_77, 14);
x_115 = lean_ctor_get(x_77, 15);
x_116 = lean_ctor_get(x_77, 16);
x_117 = lean_ctor_get(x_77, 17);
x_118 = lean_ctor_get(x_77, 18);
x_119 = lean_ctor_get(x_77, 19);
x_120 = lean_ctor_get(x_77, 20);
x_121 = lean_ctor_get(x_77, 21);
x_122 = lean_ctor_get(x_77, 22);
x_123 = lean_ctor_get(x_77, 23);
x_124 = lean_ctor_get(x_77, 24);
x_125 = lean_ctor_get(x_77, 25);
x_126 = lean_ctor_get(x_77, 26);
x_127 = lean_ctor_get(x_77, 27);
x_128 = lean_ctor_get(x_77, 28);
x_129 = lean_ctor_get(x_77, 29);
x_130 = lean_ctor_get(x_77, 30);
x_131 = lean_ctor_get(x_77, 31);
x_132 = lean_ctor_get(x_77, 32);
x_133 = lean_ctor_get(x_77, 33);
x_134 = lean_ctor_get_uint8(x_77, sizeof(void*)*40);
x_135 = lean_ctor_get(x_77, 34);
x_136 = lean_ctor_get(x_77, 35);
x_137 = lean_ctor_get(x_77, 36);
x_138 = lean_ctor_get(x_77, 37);
x_139 = lean_ctor_get(x_77, 38);
x_140 = lean_ctor_get(x_77, 39);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
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
lean_dec(x_77);
x_141 = lean_box(0);
x_142 = lean_array_fset(x_49, x_3, x_141);
lean_inc_ref(x_1);
x_143 = l_Lean_PersistentArray_push___redArg(x_128, x_1);
lean_inc(x_27);
lean_inc_ref(x_1);
x_144 = l_Lean_PersistentHashMap_insert___redArg(x_19, x_20, x_129, x_1, x_27);
x_145 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_146 = l_Lean_PersistentArray_push___redArg(x_130, x_145);
x_147 = l_Lean_PersistentArray_push___redArg(x_131, x_145);
x_148 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6;
x_149 = l_Lean_PersistentArray_push___redArg(x_132, x_148);
x_150 = lean_box(0);
x_151 = l_Lean_PersistentArray_push___redArg(x_137, x_150);
x_152 = lean_box(1);
x_153 = l_Lean_PersistentArray_push___redArg(x_139, x_152);
x_154 = lean_alloc_ctor(0, 40, 1);
lean_ctor_set(x_154, 0, x_100);
lean_ctor_set(x_154, 1, x_101);
lean_ctor_set(x_154, 2, x_102);
lean_ctor_set(x_154, 3, x_103);
lean_ctor_set(x_154, 4, x_104);
lean_ctor_set(x_154, 5, x_105);
lean_ctor_set(x_154, 6, x_106);
lean_ctor_set(x_154, 7, x_107);
lean_ctor_set(x_154, 8, x_108);
lean_ctor_set(x_154, 9, x_109);
lean_ctor_set(x_154, 10, x_110);
lean_ctor_set(x_154, 11, x_111);
lean_ctor_set(x_154, 12, x_112);
lean_ctor_set(x_154, 13, x_113);
lean_ctor_set(x_154, 14, x_114);
lean_ctor_set(x_154, 15, x_115);
lean_ctor_set(x_154, 16, x_116);
lean_ctor_set(x_154, 17, x_117);
lean_ctor_set(x_154, 18, x_118);
lean_ctor_set(x_154, 19, x_119);
lean_ctor_set(x_154, 20, x_120);
lean_ctor_set(x_154, 21, x_121);
lean_ctor_set(x_154, 22, x_122);
lean_ctor_set(x_154, 23, x_123);
lean_ctor_set(x_154, 24, x_124);
lean_ctor_set(x_154, 25, x_125);
lean_ctor_set(x_154, 26, x_126);
lean_ctor_set(x_154, 27, x_127);
lean_ctor_set(x_154, 28, x_143);
lean_ctor_set(x_154, 29, x_144);
lean_ctor_set(x_154, 30, x_146);
lean_ctor_set(x_154, 31, x_147);
lean_ctor_set(x_154, 32, x_149);
lean_ctor_set(x_154, 33, x_133);
lean_ctor_set(x_154, 34, x_135);
lean_ctor_set(x_154, 35, x_136);
lean_ctor_set(x_154, 36, x_151);
lean_ctor_set(x_154, 37, x_138);
lean_ctor_set(x_154, 38, x_153);
lean_ctor_set(x_154, 39, x_140);
lean_ctor_set_uint8(x_154, sizeof(void*)*40, x_134);
x_155 = lean_array_fset(x_142, x_3, x_154);
x_53 = x_155;
goto block_74;
}
}
block_74:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 3, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
lean_ctor_set(x_54, 2, x_51);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 4, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_46);
lean_ctor_set(x_55, 2, x_47);
lean_ctor_set(x_55, 3, x_54);
if (lean_is_scalar(x_44)) {
 x_56 = lean_alloc_ctor(0, 16, 1);
} else {
 x_56 = x_44;
}
lean_ctor_set(x_56, 0, x_28);
lean_ctor_set(x_56, 1, x_29);
lean_ctor_set(x_56, 2, x_30);
lean_ctor_set(x_56, 3, x_31);
lean_ctor_set(x_56, 4, x_32);
lean_ctor_set(x_56, 5, x_33);
lean_ctor_set(x_56, 6, x_34);
lean_ctor_set(x_56, 7, x_35);
lean_ctor_set(x_56, 8, x_37);
lean_ctor_set(x_56, 9, x_38);
lean_ctor_set(x_56, 10, x_39);
lean_ctor_set(x_56, 11, x_40);
lean_ctor_set(x_56, 12, x_41);
lean_ctor_set(x_56, 13, x_42);
lean_ctor_set(x_56, 14, x_55);
lean_ctor_set(x_56, 15, x_43);
lean_ctor_set_uint8(x_56, sizeof(void*)*16, x_36);
x_57 = lean_st_ref_set(x_4, x_56, x_26);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc_ref(x_1);
x_59 = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
if (x_2 == 0)
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
lean_ctor_set(x_59, 0, x_27);
return x_59;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_27);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec_ref(x_59);
x_65 = l_Lean_Meta_Grind_markAsLinarithTerm(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_27);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_27);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_27);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
lean_object* x_156; 
lean_dec_ref(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_21, 0);
lean_inc(x_156);
lean_dec_ref(x_21);
lean_ctor_set(x_13, 0, x_156);
return x_13;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_13, 0);
x_158 = lean_ctor_get(x_13, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_13);
x_159 = lean_ctor_get(x_157, 28);
lean_inc_ref(x_159);
x_160 = lean_ctor_get(x_157, 29);
lean_inc_ref(x_160);
lean_dec(x_157);
x_161 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__0;
x_162 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__1;
lean_inc_ref(x_1);
x_163 = l_Lean_PersistentHashMap_find_x3f___redArg(x_161, x_162, x_160, x_1);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_215; uint8_t x_216; 
x_164 = lean_st_ref_take(x_4, x_158);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 14);
lean_inc_ref(x_166);
x_167 = lean_ctor_get(x_166, 3);
lean_inc_ref(x_167);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
lean_dec_ref(x_164);
x_169 = lean_ctor_get(x_159, 2);
lean_inc(x_169);
lean_dec_ref(x_159);
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 1);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_165, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_165, 3);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_165, 4);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_165, 5);
lean_inc_ref(x_175);
x_176 = lean_ctor_get(x_165, 6);
lean_inc_ref(x_176);
x_177 = lean_ctor_get(x_165, 7);
lean_inc_ref(x_177);
x_178 = lean_ctor_get_uint8(x_165, sizeof(void*)*16);
x_179 = lean_ctor_get(x_165, 8);
lean_inc(x_179);
x_180 = lean_ctor_get(x_165, 9);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_165, 10);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_165, 11);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_165, 12);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_165, 13);
lean_inc_ref(x_184);
x_185 = lean_ctor_get(x_165, 15);
lean_inc_ref(x_185);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 lean_ctor_release(x_165, 5);
 lean_ctor_release(x_165, 6);
 lean_ctor_release(x_165, 7);
 lean_ctor_release(x_165, 8);
 lean_ctor_release(x_165, 9);
 lean_ctor_release(x_165, 10);
 lean_ctor_release(x_165, 11);
 lean_ctor_release(x_165, 12);
 lean_ctor_release(x_165, 13);
 lean_ctor_release(x_165, 14);
 lean_ctor_release(x_165, 15);
 x_186 = x_165;
} else {
 lean_dec_ref(x_165);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_166, 0);
lean_inc_ref(x_187);
x_188 = lean_ctor_get(x_166, 1);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_166, 2);
lean_inc_ref(x_189);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 lean_ctor_release(x_166, 3);
 x_190 = x_166;
} else {
 lean_dec_ref(x_166);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_167, 1);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_167, 2);
lean_inc_ref(x_193);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_194 = x_167;
} else {
 lean_dec_ref(x_167);
 x_194 = lean_box(0);
}
x_215 = lean_array_get_size(x_191);
x_216 = lean_nat_dec_lt(x_3, x_215);
lean_dec(x_215);
if (x_216 == 0)
{
x_195 = x_191;
goto block_214;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_217 = lean_array_fget(x_191, x_3);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_217, 2);
lean_inc_ref(x_220);
x_221 = lean_ctor_get(x_217, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_217, 4);
lean_inc_ref(x_222);
x_223 = lean_ctor_get(x_217, 5);
lean_inc(x_223);
x_224 = lean_ctor_get(x_217, 6);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 7);
lean_inc(x_225);
x_226 = lean_ctor_get(x_217, 8);
lean_inc(x_226);
x_227 = lean_ctor_get(x_217, 9);
lean_inc(x_227);
x_228 = lean_ctor_get(x_217, 10);
lean_inc(x_228);
x_229 = lean_ctor_get(x_217, 11);
lean_inc(x_229);
x_230 = lean_ctor_get(x_217, 12);
lean_inc(x_230);
x_231 = lean_ctor_get(x_217, 13);
lean_inc(x_231);
x_232 = lean_ctor_get(x_217, 14);
lean_inc(x_232);
x_233 = lean_ctor_get(x_217, 15);
lean_inc_ref(x_233);
x_234 = lean_ctor_get(x_217, 16);
lean_inc_ref(x_234);
x_235 = lean_ctor_get(x_217, 17);
lean_inc(x_235);
x_236 = lean_ctor_get(x_217, 18);
lean_inc(x_236);
x_237 = lean_ctor_get(x_217, 19);
lean_inc(x_237);
x_238 = lean_ctor_get(x_217, 20);
lean_inc_ref(x_238);
x_239 = lean_ctor_get(x_217, 21);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_217, 22);
lean_inc_ref(x_240);
x_241 = lean_ctor_get(x_217, 23);
lean_inc(x_241);
x_242 = lean_ctor_get(x_217, 24);
lean_inc(x_242);
x_243 = lean_ctor_get(x_217, 25);
lean_inc(x_243);
x_244 = lean_ctor_get(x_217, 26);
lean_inc_ref(x_244);
x_245 = lean_ctor_get(x_217, 27);
lean_inc_ref(x_245);
x_246 = lean_ctor_get(x_217, 28);
lean_inc_ref(x_246);
x_247 = lean_ctor_get(x_217, 29);
lean_inc_ref(x_247);
x_248 = lean_ctor_get(x_217, 30);
lean_inc_ref(x_248);
x_249 = lean_ctor_get(x_217, 31);
lean_inc_ref(x_249);
x_250 = lean_ctor_get(x_217, 32);
lean_inc_ref(x_250);
x_251 = lean_ctor_get(x_217, 33);
lean_inc_ref(x_251);
x_252 = lean_ctor_get_uint8(x_217, sizeof(void*)*40);
x_253 = lean_ctor_get(x_217, 34);
lean_inc(x_253);
x_254 = lean_ctor_get(x_217, 35);
lean_inc_ref(x_254);
x_255 = lean_ctor_get(x_217, 36);
lean_inc_ref(x_255);
x_256 = lean_ctor_get(x_217, 37);
lean_inc(x_256);
x_257 = lean_ctor_get(x_217, 38);
lean_inc_ref(x_257);
x_258 = lean_ctor_get(x_217, 39);
lean_inc_ref(x_258);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 lean_ctor_release(x_217, 2);
 lean_ctor_release(x_217, 3);
 lean_ctor_release(x_217, 4);
 lean_ctor_release(x_217, 5);
 lean_ctor_release(x_217, 6);
 lean_ctor_release(x_217, 7);
 lean_ctor_release(x_217, 8);
 lean_ctor_release(x_217, 9);
 lean_ctor_release(x_217, 10);
 lean_ctor_release(x_217, 11);
 lean_ctor_release(x_217, 12);
 lean_ctor_release(x_217, 13);
 lean_ctor_release(x_217, 14);
 lean_ctor_release(x_217, 15);
 lean_ctor_release(x_217, 16);
 lean_ctor_release(x_217, 17);
 lean_ctor_release(x_217, 18);
 lean_ctor_release(x_217, 19);
 lean_ctor_release(x_217, 20);
 lean_ctor_release(x_217, 21);
 lean_ctor_release(x_217, 22);
 lean_ctor_release(x_217, 23);
 lean_ctor_release(x_217, 24);
 lean_ctor_release(x_217, 25);
 lean_ctor_release(x_217, 26);
 lean_ctor_release(x_217, 27);
 lean_ctor_release(x_217, 28);
 lean_ctor_release(x_217, 29);
 lean_ctor_release(x_217, 30);
 lean_ctor_release(x_217, 31);
 lean_ctor_release(x_217, 32);
 lean_ctor_release(x_217, 33);
 lean_ctor_release(x_217, 34);
 lean_ctor_release(x_217, 35);
 lean_ctor_release(x_217, 36);
 lean_ctor_release(x_217, 37);
 lean_ctor_release(x_217, 38);
 lean_ctor_release(x_217, 39);
 x_259 = x_217;
} else {
 lean_dec_ref(x_217);
 x_259 = lean_box(0);
}
x_260 = lean_box(0);
x_261 = lean_array_fset(x_191, x_3, x_260);
lean_inc_ref(x_1);
x_262 = l_Lean_PersistentArray_push___redArg(x_246, x_1);
lean_inc(x_169);
lean_inc_ref(x_1);
x_263 = l_Lean_PersistentHashMap_insert___redArg(x_161, x_162, x_247, x_1, x_169);
x_264 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__4;
x_265 = l_Lean_PersistentArray_push___redArg(x_248, x_264);
x_266 = l_Lean_PersistentArray_push___redArg(x_249, x_264);
x_267 = l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6;
x_268 = l_Lean_PersistentArray_push___redArg(x_250, x_267);
x_269 = lean_box(0);
x_270 = l_Lean_PersistentArray_push___redArg(x_255, x_269);
x_271 = lean_box(1);
x_272 = l_Lean_PersistentArray_push___redArg(x_257, x_271);
if (lean_is_scalar(x_259)) {
 x_273 = lean_alloc_ctor(0, 40, 1);
} else {
 x_273 = x_259;
}
lean_ctor_set(x_273, 0, x_218);
lean_ctor_set(x_273, 1, x_219);
lean_ctor_set(x_273, 2, x_220);
lean_ctor_set(x_273, 3, x_221);
lean_ctor_set(x_273, 4, x_222);
lean_ctor_set(x_273, 5, x_223);
lean_ctor_set(x_273, 6, x_224);
lean_ctor_set(x_273, 7, x_225);
lean_ctor_set(x_273, 8, x_226);
lean_ctor_set(x_273, 9, x_227);
lean_ctor_set(x_273, 10, x_228);
lean_ctor_set(x_273, 11, x_229);
lean_ctor_set(x_273, 12, x_230);
lean_ctor_set(x_273, 13, x_231);
lean_ctor_set(x_273, 14, x_232);
lean_ctor_set(x_273, 15, x_233);
lean_ctor_set(x_273, 16, x_234);
lean_ctor_set(x_273, 17, x_235);
lean_ctor_set(x_273, 18, x_236);
lean_ctor_set(x_273, 19, x_237);
lean_ctor_set(x_273, 20, x_238);
lean_ctor_set(x_273, 21, x_239);
lean_ctor_set(x_273, 22, x_240);
lean_ctor_set(x_273, 23, x_241);
lean_ctor_set(x_273, 24, x_242);
lean_ctor_set(x_273, 25, x_243);
lean_ctor_set(x_273, 26, x_244);
lean_ctor_set(x_273, 27, x_245);
lean_ctor_set(x_273, 28, x_262);
lean_ctor_set(x_273, 29, x_263);
lean_ctor_set(x_273, 30, x_265);
lean_ctor_set(x_273, 31, x_266);
lean_ctor_set(x_273, 32, x_268);
lean_ctor_set(x_273, 33, x_251);
lean_ctor_set(x_273, 34, x_253);
lean_ctor_set(x_273, 35, x_254);
lean_ctor_set(x_273, 36, x_270);
lean_ctor_set(x_273, 37, x_256);
lean_ctor_set(x_273, 38, x_272);
lean_ctor_set(x_273, 39, x_258);
lean_ctor_set_uint8(x_273, sizeof(void*)*40, x_252);
x_274 = lean_array_fset(x_261, x_3, x_273);
x_195 = x_274;
goto block_214;
}
block_214:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 3, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_192);
lean_ctor_set(x_196, 2, x_193);
if (lean_is_scalar(x_190)) {
 x_197 = lean_alloc_ctor(0, 4, 0);
} else {
 x_197 = x_190;
}
lean_ctor_set(x_197, 0, x_187);
lean_ctor_set(x_197, 1, x_188);
lean_ctor_set(x_197, 2, x_189);
lean_ctor_set(x_197, 3, x_196);
if (lean_is_scalar(x_186)) {
 x_198 = lean_alloc_ctor(0, 16, 1);
} else {
 x_198 = x_186;
}
lean_ctor_set(x_198, 0, x_170);
lean_ctor_set(x_198, 1, x_171);
lean_ctor_set(x_198, 2, x_172);
lean_ctor_set(x_198, 3, x_173);
lean_ctor_set(x_198, 4, x_174);
lean_ctor_set(x_198, 5, x_175);
lean_ctor_set(x_198, 6, x_176);
lean_ctor_set(x_198, 7, x_177);
lean_ctor_set(x_198, 8, x_179);
lean_ctor_set(x_198, 9, x_180);
lean_ctor_set(x_198, 10, x_181);
lean_ctor_set(x_198, 11, x_182);
lean_ctor_set(x_198, 12, x_183);
lean_ctor_set(x_198, 13, x_184);
lean_ctor_set(x_198, 14, x_197);
lean_ctor_set(x_198, 15, x_185);
lean_ctor_set_uint8(x_198, sizeof(void*)*16, x_178);
x_199 = lean_st_ref_set(x_4, x_198, x_168);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec_ref(x_199);
lean_inc_ref(x_1);
x_201 = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_200);
if (x_2 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_1);
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
lean_ctor_set(x_204, 0, x_169);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_201, 1);
lean_inc(x_205);
lean_dec_ref(x_201);
x_206 = l_Lean_Meta_Grind_markAsLinarithTerm(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_169);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_169);
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_206, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_212 = x_206;
} else {
 lean_dec_ref(x_206);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
else
{
lean_object* x_275; lean_object* x_276; 
lean_dec_ref(x_159);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_275 = lean_ctor_get(x_163, 0);
lean_inc(x_275);
lean_dec_ref(x_163);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_158);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_277 = !lean_is_exclusive(x_13);
if (x_277 == 0)
{
return x_13;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_13, 0);
x_279 = lean_ctor_get(x_13, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_13);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_mkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
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
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__5);
l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6 = _init_l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_mkVar___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
