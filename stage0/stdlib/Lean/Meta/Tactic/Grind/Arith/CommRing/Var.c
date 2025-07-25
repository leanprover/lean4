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
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsCommRingTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkSVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_getSemiring(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqExprPtr___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableExprPtr___lam__0___boxed), 1, 0);
return x_1;
}
}
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 20);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 21);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0;
x_19 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1;
lean_inc_ref(x_1);
x_20 = l_Lean_PersistentHashMap_find_x3f___redArg(x_18, x_19, x_17, x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_75; uint8_t x_76; 
lean_free_object(x_12);
x_21 = lean_st_ref_take(x_3, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 14);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = lean_ctor_get(x_16, 2);
lean_inc(x_26);
lean_dec_ref(x_16);
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_22, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_22, 5);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_22, 6);
lean_inc_ref(x_34);
x_35 = lean_ctor_get(x_22, 7);
lean_inc_ref(x_35);
x_36 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_37 = lean_ctor_get(x_22, 8);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 9);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_22, 10);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_22, 11);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_22, 12);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_22, 13);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_22, 15);
lean_inc_ref(x_43);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 lean_ctor_release(x_22, 6);
 lean_ctor_release(x_22, 7);
 lean_ctor_release(x_22, 8);
 lean_ctor_release(x_22, 9);
 lean_ctor_release(x_22, 10);
 lean_ctor_release(x_22, 11);
 lean_ctor_release(x_22, 12);
 lean_ctor_release(x_22, 13);
 lean_ctor_release(x_22, 14);
 lean_ctor_release(x_22, 15);
 x_44 = x_22;
} else {
 lean_dec_ref(x_22);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_46);
x_47 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_47);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_48 = x_23;
} else {
 lean_dec_ref(x_23);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_24, 4);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_24, 5);
lean_inc_ref(x_54);
x_55 = lean_ctor_get(x_24, 6);
lean_inc(x_55);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 x_56 = x_24;
} else {
 lean_dec_ref(x_24);
 x_56 = lean_box(0);
}
x_75 = lean_array_get_size(x_49);
x_76 = lean_nat_dec_lt(x_27, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_dec(x_27);
x_57 = x_49;
goto block_74;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_array_fget(x_49, x_27);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_77, 20);
x_80 = lean_ctor_get(x_77, 21);
x_81 = lean_box(0);
x_82 = lean_array_fset(x_49, x_27, x_81);
lean_inc_ref(x_1);
x_83 = l_Lean_PersistentArray_push___redArg(x_79, x_1);
lean_inc(x_26);
lean_inc_ref(x_1);
x_84 = l_Lean_PersistentHashMap_insert___redArg(x_18, x_19, x_80, x_1, x_26);
lean_ctor_set(x_77, 21, x_84);
lean_ctor_set(x_77, 20, x_83);
x_85 = lean_array_fset(x_82, x_27, x_77);
lean_dec(x_27);
x_57 = x_85;
goto block_74;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
x_88 = lean_ctor_get(x_77, 2);
x_89 = lean_ctor_get(x_77, 3);
x_90 = lean_ctor_get(x_77, 4);
x_91 = lean_ctor_get(x_77, 5);
x_92 = lean_ctor_get(x_77, 6);
x_93 = lean_ctor_get(x_77, 7);
x_94 = lean_ctor_get(x_77, 8);
x_95 = lean_ctor_get(x_77, 9);
x_96 = lean_ctor_get(x_77, 10);
x_97 = lean_ctor_get(x_77, 11);
x_98 = lean_ctor_get(x_77, 12);
x_99 = lean_ctor_get(x_77, 13);
x_100 = lean_ctor_get(x_77, 14);
x_101 = lean_ctor_get(x_77, 15);
x_102 = lean_ctor_get(x_77, 16);
x_103 = lean_ctor_get(x_77, 17);
x_104 = lean_ctor_get(x_77, 18);
x_105 = lean_ctor_get(x_77, 19);
x_106 = lean_ctor_get(x_77, 20);
x_107 = lean_ctor_get(x_77, 21);
x_108 = lean_ctor_get(x_77, 22);
x_109 = lean_ctor_get(x_77, 23);
x_110 = lean_ctor_get(x_77, 24);
x_111 = lean_ctor_get(x_77, 25);
x_112 = lean_ctor_get(x_77, 26);
x_113 = lean_ctor_get(x_77, 27);
x_114 = lean_ctor_get_uint8(x_77, sizeof(void*)*30);
x_115 = lean_ctor_get(x_77, 28);
x_116 = lean_ctor_get(x_77, 29);
x_117 = lean_ctor_get_uint8(x_77, sizeof(void*)*30 + 1);
lean_inc(x_116);
lean_inc(x_115);
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
lean_dec(x_77);
x_118 = lean_box(0);
x_119 = lean_array_fset(x_49, x_27, x_118);
lean_inc_ref(x_1);
x_120 = l_Lean_PersistentArray_push___redArg(x_106, x_1);
lean_inc(x_26);
lean_inc_ref(x_1);
x_121 = l_Lean_PersistentHashMap_insert___redArg(x_18, x_19, x_107, x_1, x_26);
x_122 = lean_alloc_ctor(0, 30, 2);
lean_ctor_set(x_122, 0, x_86);
lean_ctor_set(x_122, 1, x_87);
lean_ctor_set(x_122, 2, x_88);
lean_ctor_set(x_122, 3, x_89);
lean_ctor_set(x_122, 4, x_90);
lean_ctor_set(x_122, 5, x_91);
lean_ctor_set(x_122, 6, x_92);
lean_ctor_set(x_122, 7, x_93);
lean_ctor_set(x_122, 8, x_94);
lean_ctor_set(x_122, 9, x_95);
lean_ctor_set(x_122, 10, x_96);
lean_ctor_set(x_122, 11, x_97);
lean_ctor_set(x_122, 12, x_98);
lean_ctor_set(x_122, 13, x_99);
lean_ctor_set(x_122, 14, x_100);
lean_ctor_set(x_122, 15, x_101);
lean_ctor_set(x_122, 16, x_102);
lean_ctor_set(x_122, 17, x_103);
lean_ctor_set(x_122, 18, x_104);
lean_ctor_set(x_122, 19, x_105);
lean_ctor_set(x_122, 20, x_120);
lean_ctor_set(x_122, 21, x_121);
lean_ctor_set(x_122, 22, x_108);
lean_ctor_set(x_122, 23, x_109);
lean_ctor_set(x_122, 24, x_110);
lean_ctor_set(x_122, 25, x_111);
lean_ctor_set(x_122, 26, x_112);
lean_ctor_set(x_122, 27, x_113);
lean_ctor_set(x_122, 28, x_115);
lean_ctor_set(x_122, 29, x_116);
lean_ctor_set_uint8(x_122, sizeof(void*)*30, x_114);
lean_ctor_set_uint8(x_122, sizeof(void*)*30 + 1, x_117);
x_123 = lean_array_fset(x_119, x_27, x_122);
lean_dec(x_27);
x_57 = x_123;
goto block_74;
}
}
block_74:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 7, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_55);
if (lean_is_scalar(x_48)) {
 x_59 = lean_alloc_ctor(0, 4, 0);
} else {
 x_59 = x_48;
}
lean_ctor_set(x_59, 0, x_45);
lean_ctor_set(x_59, 1, x_46);
lean_ctor_set(x_59, 2, x_58);
lean_ctor_set(x_59, 3, x_47);
if (lean_is_scalar(x_44)) {
 x_60 = lean_alloc_ctor(0, 16, 1);
} else {
 x_60 = x_44;
}
lean_ctor_set(x_60, 0, x_28);
lean_ctor_set(x_60, 1, x_29);
lean_ctor_set(x_60, 2, x_30);
lean_ctor_set(x_60, 3, x_31);
lean_ctor_set(x_60, 4, x_32);
lean_ctor_set(x_60, 5, x_33);
lean_ctor_set(x_60, 6, x_34);
lean_ctor_set(x_60, 7, x_35);
lean_ctor_set(x_60, 8, x_37);
lean_ctor_set(x_60, 9, x_38);
lean_ctor_set(x_60, 10, x_39);
lean_ctor_set(x_60, 11, x_40);
lean_ctor_set(x_60, 12, x_41);
lean_ctor_set(x_60, 13, x_42);
lean_ctor_set(x_60, 14, x_59);
lean_ctor_set(x_60, 15, x_43);
lean_ctor_set_uint8(x_60, sizeof(void*)*16, x_36);
x_61 = lean_st_ref_set(x_3, x_60, x_25);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc_ref(x_1);
x_63 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_26);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_26);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_26);
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
else
{
lean_object* x_124; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_20, 0);
lean_inc(x_124);
lean_dec_ref(x_20);
lean_ctor_set(x_12, 0, x_124);
return x_12;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_12, 0);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_12);
x_127 = lean_ctor_get(x_125, 20);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 21);
lean_inc_ref(x_128);
lean_dec(x_125);
x_129 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0;
x_130 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1;
lean_inc_ref(x_1);
x_131 = l_Lean_PersistentHashMap_find_x3f___redArg(x_129, x_130, x_128, x_1);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_185; uint8_t x_186; 
x_132 = lean_st_ref_take(x_3, x_126);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_133, 14);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_134, 2);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
lean_dec_ref(x_132);
x_137 = lean_ctor_get(x_127, 2);
lean_inc(x_137);
lean_dec_ref(x_127);
x_138 = lean_ctor_get(x_2, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 1);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_133, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_133, 3);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_133, 4);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_133, 5);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_133, 6);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_133, 7);
lean_inc_ref(x_146);
x_147 = lean_ctor_get_uint8(x_133, sizeof(void*)*16);
x_148 = lean_ctor_get(x_133, 8);
lean_inc(x_148);
x_149 = lean_ctor_get(x_133, 9);
lean_inc_ref(x_149);
x_150 = lean_ctor_get(x_133, 10);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_133, 11);
lean_inc_ref(x_151);
x_152 = lean_ctor_get(x_133, 12);
lean_inc_ref(x_152);
x_153 = lean_ctor_get(x_133, 13);
lean_inc_ref(x_153);
x_154 = lean_ctor_get(x_133, 15);
lean_inc_ref(x_154);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 lean_ctor_release(x_133, 2);
 lean_ctor_release(x_133, 3);
 lean_ctor_release(x_133, 4);
 lean_ctor_release(x_133, 5);
 lean_ctor_release(x_133, 6);
 lean_ctor_release(x_133, 7);
 lean_ctor_release(x_133, 8);
 lean_ctor_release(x_133, 9);
 lean_ctor_release(x_133, 10);
 lean_ctor_release(x_133, 11);
 lean_ctor_release(x_133, 12);
 lean_ctor_release(x_133, 13);
 lean_ctor_release(x_133, 14);
 lean_ctor_release(x_133, 15);
 x_155 = x_133;
} else {
 lean_dec_ref(x_133);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_134, 0);
lean_inc_ref(x_156);
x_157 = lean_ctor_get(x_134, 1);
lean_inc_ref(x_157);
x_158 = lean_ctor_get(x_134, 3);
lean_inc_ref(x_158);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 lean_ctor_release(x_134, 2);
 lean_ctor_release(x_134, 3);
 x_159 = x_134;
} else {
 lean_dec_ref(x_134);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_160);
x_161 = lean_ctor_get(x_135, 1);
lean_inc_ref(x_161);
x_162 = lean_ctor_get(x_135, 2);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_135, 3);
lean_inc_ref(x_163);
x_164 = lean_ctor_get(x_135, 4);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_135, 5);
lean_inc_ref(x_165);
x_166 = lean_ctor_get(x_135, 6);
lean_inc(x_166);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 lean_ctor_release(x_135, 2);
 lean_ctor_release(x_135, 3);
 lean_ctor_release(x_135, 4);
 lean_ctor_release(x_135, 5);
 lean_ctor_release(x_135, 6);
 x_167 = x_135;
} else {
 lean_dec_ref(x_135);
 x_167 = lean_box(0);
}
x_185 = lean_array_get_size(x_160);
x_186 = lean_nat_dec_lt(x_138, x_185);
lean_dec(x_185);
if (x_186 == 0)
{
lean_dec(x_138);
x_168 = x_160;
goto block_184;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_187 = lean_array_fget(x_160, x_138);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 2);
lean_inc_ref(x_190);
x_191 = lean_ctor_get(x_187, 3);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 4);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_187, 5);
lean_inc_ref(x_193);
x_194 = lean_ctor_get(x_187, 6);
lean_inc_ref(x_194);
x_195 = lean_ctor_get(x_187, 7);
lean_inc_ref(x_195);
x_196 = lean_ctor_get(x_187, 8);
lean_inc(x_196);
x_197 = lean_ctor_get(x_187, 9);
lean_inc(x_197);
x_198 = lean_ctor_get(x_187, 10);
lean_inc(x_198);
x_199 = lean_ctor_get(x_187, 11);
lean_inc(x_199);
x_200 = lean_ctor_get(x_187, 12);
lean_inc(x_200);
x_201 = lean_ctor_get(x_187, 13);
lean_inc(x_201);
x_202 = lean_ctor_get(x_187, 14);
lean_inc(x_202);
x_203 = lean_ctor_get(x_187, 15);
lean_inc(x_203);
x_204 = lean_ctor_get(x_187, 16);
lean_inc(x_204);
x_205 = lean_ctor_get(x_187, 17);
lean_inc(x_205);
x_206 = lean_ctor_get(x_187, 18);
lean_inc(x_206);
x_207 = lean_ctor_get(x_187, 19);
lean_inc(x_207);
x_208 = lean_ctor_get(x_187, 20);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_187, 21);
lean_inc_ref(x_209);
x_210 = lean_ctor_get(x_187, 22);
lean_inc_ref(x_210);
x_211 = lean_ctor_get(x_187, 23);
lean_inc(x_211);
x_212 = lean_ctor_get(x_187, 24);
lean_inc(x_212);
x_213 = lean_ctor_get(x_187, 25);
lean_inc(x_213);
x_214 = lean_ctor_get(x_187, 26);
lean_inc(x_214);
x_215 = lean_ctor_get(x_187, 27);
lean_inc_ref(x_215);
x_216 = lean_ctor_get_uint8(x_187, sizeof(void*)*30);
x_217 = lean_ctor_get(x_187, 28);
lean_inc_ref(x_217);
x_218 = lean_ctor_get(x_187, 29);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_187, sizeof(void*)*30 + 1);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 lean_ctor_release(x_187, 2);
 lean_ctor_release(x_187, 3);
 lean_ctor_release(x_187, 4);
 lean_ctor_release(x_187, 5);
 lean_ctor_release(x_187, 6);
 lean_ctor_release(x_187, 7);
 lean_ctor_release(x_187, 8);
 lean_ctor_release(x_187, 9);
 lean_ctor_release(x_187, 10);
 lean_ctor_release(x_187, 11);
 lean_ctor_release(x_187, 12);
 lean_ctor_release(x_187, 13);
 lean_ctor_release(x_187, 14);
 lean_ctor_release(x_187, 15);
 lean_ctor_release(x_187, 16);
 lean_ctor_release(x_187, 17);
 lean_ctor_release(x_187, 18);
 lean_ctor_release(x_187, 19);
 lean_ctor_release(x_187, 20);
 lean_ctor_release(x_187, 21);
 lean_ctor_release(x_187, 22);
 lean_ctor_release(x_187, 23);
 lean_ctor_release(x_187, 24);
 lean_ctor_release(x_187, 25);
 lean_ctor_release(x_187, 26);
 lean_ctor_release(x_187, 27);
 lean_ctor_release(x_187, 28);
 lean_ctor_release(x_187, 29);
 x_220 = x_187;
} else {
 lean_dec_ref(x_187);
 x_220 = lean_box(0);
}
x_221 = lean_box(0);
x_222 = lean_array_fset(x_160, x_138, x_221);
lean_inc_ref(x_1);
x_223 = l_Lean_PersistentArray_push___redArg(x_208, x_1);
lean_inc(x_137);
lean_inc_ref(x_1);
x_224 = l_Lean_PersistentHashMap_insert___redArg(x_129, x_130, x_209, x_1, x_137);
if (lean_is_scalar(x_220)) {
 x_225 = lean_alloc_ctor(0, 30, 2);
} else {
 x_225 = x_220;
}
lean_ctor_set(x_225, 0, x_188);
lean_ctor_set(x_225, 1, x_189);
lean_ctor_set(x_225, 2, x_190);
lean_ctor_set(x_225, 3, x_191);
lean_ctor_set(x_225, 4, x_192);
lean_ctor_set(x_225, 5, x_193);
lean_ctor_set(x_225, 6, x_194);
lean_ctor_set(x_225, 7, x_195);
lean_ctor_set(x_225, 8, x_196);
lean_ctor_set(x_225, 9, x_197);
lean_ctor_set(x_225, 10, x_198);
lean_ctor_set(x_225, 11, x_199);
lean_ctor_set(x_225, 12, x_200);
lean_ctor_set(x_225, 13, x_201);
lean_ctor_set(x_225, 14, x_202);
lean_ctor_set(x_225, 15, x_203);
lean_ctor_set(x_225, 16, x_204);
lean_ctor_set(x_225, 17, x_205);
lean_ctor_set(x_225, 18, x_206);
lean_ctor_set(x_225, 19, x_207);
lean_ctor_set(x_225, 20, x_223);
lean_ctor_set(x_225, 21, x_224);
lean_ctor_set(x_225, 22, x_210);
lean_ctor_set(x_225, 23, x_211);
lean_ctor_set(x_225, 24, x_212);
lean_ctor_set(x_225, 25, x_213);
lean_ctor_set(x_225, 26, x_214);
lean_ctor_set(x_225, 27, x_215);
lean_ctor_set(x_225, 28, x_217);
lean_ctor_set(x_225, 29, x_218);
lean_ctor_set_uint8(x_225, sizeof(void*)*30, x_216);
lean_ctor_set_uint8(x_225, sizeof(void*)*30 + 1, x_219);
x_226 = lean_array_fset(x_222, x_138, x_225);
lean_dec(x_138);
x_168 = x_226;
goto block_184;
}
block_184:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
if (lean_is_scalar(x_167)) {
 x_169 = lean_alloc_ctor(0, 7, 0);
} else {
 x_169 = x_167;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_161);
lean_ctor_set(x_169, 2, x_162);
lean_ctor_set(x_169, 3, x_163);
lean_ctor_set(x_169, 4, x_164);
lean_ctor_set(x_169, 5, x_165);
lean_ctor_set(x_169, 6, x_166);
if (lean_is_scalar(x_159)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_159;
}
lean_ctor_set(x_170, 0, x_156);
lean_ctor_set(x_170, 1, x_157);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_158);
if (lean_is_scalar(x_155)) {
 x_171 = lean_alloc_ctor(0, 16, 1);
} else {
 x_171 = x_155;
}
lean_ctor_set(x_171, 0, x_139);
lean_ctor_set(x_171, 1, x_140);
lean_ctor_set(x_171, 2, x_141);
lean_ctor_set(x_171, 3, x_142);
lean_ctor_set(x_171, 4, x_143);
lean_ctor_set(x_171, 5, x_144);
lean_ctor_set(x_171, 6, x_145);
lean_ctor_set(x_171, 7, x_146);
lean_ctor_set(x_171, 8, x_148);
lean_ctor_set(x_171, 9, x_149);
lean_ctor_set(x_171, 10, x_150);
lean_ctor_set(x_171, 11, x_151);
lean_ctor_set(x_171, 12, x_152);
lean_ctor_set(x_171, 13, x_153);
lean_ctor_set(x_171, 14, x_170);
lean_ctor_set(x_171, 15, x_154);
lean_ctor_set_uint8(x_171, sizeof(void*)*16, x_147);
x_172 = lean_st_ref_set(x_3, x_171, x_136);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec_ref(x_172);
lean_inc_ref(x_1);
x_174 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec_ref(x_174);
x_176 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_137);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_137);
x_180 = lean_ctor_get(x_176, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_127);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_227 = lean_ctor_get(x_131, 0);
lean_inc(x_227);
lean_dec_ref(x_131);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_126);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_229 = !lean_is_exclusive(x_12);
if (x_229 == 0)
{
return x_12;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_12, 0);
x_231 = lean_ctor_get(x_12, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_12);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 13);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_14, 14);
lean_inc_ref(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0;
x_19 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1;
lean_inc_ref(x_1);
x_20 = l_Lean_PersistentHashMap_find_x3f___redArg(x_18, x_19, x_17, x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_74; uint8_t x_75; 
lean_free_object(x_12);
x_21 = lean_st_ref_take(x_3, x_15);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 14);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_23, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec_ref(x_21);
x_26 = lean_ctor_get(x_16, 2);
lean_inc(x_26);
lean_dec_ref(x_16);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_22, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_22, 4);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_22, 5);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_22, 6);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_22, 7);
lean_inc_ref(x_34);
x_35 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_36 = lean_ctor_get(x_22, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 9);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_22, 10);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_22, 11);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_22, 12);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_22, 13);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_22, 15);
lean_inc_ref(x_42);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 lean_ctor_release(x_22, 2);
 lean_ctor_release(x_22, 3);
 lean_ctor_release(x_22, 4);
 lean_ctor_release(x_22, 5);
 lean_ctor_release(x_22, 6);
 lean_ctor_release(x_22, 7);
 lean_ctor_release(x_22, 8);
 lean_ctor_release(x_22, 9);
 lean_ctor_release(x_22, 10);
 lean_ctor_release(x_22, 11);
 lean_ctor_release(x_22, 12);
 lean_ctor_release(x_22, 13);
 lean_ctor_release(x_22, 14);
 lean_ctor_release(x_22, 15);
 x_43 = x_22;
} else {
 lean_dec_ref(x_22);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_46);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 lean_ctor_release(x_23, 2);
 lean_ctor_release(x_23, 3);
 x_47 = x_23;
} else {
 lean_dec_ref(x_23);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_24, 4);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_24, 5);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_24, 6);
lean_inc(x_54);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 lean_ctor_release(x_24, 3);
 lean_ctor_release(x_24, 4);
 lean_ctor_release(x_24, 5);
 lean_ctor_release(x_24, 6);
 x_55 = x_24;
} else {
 lean_dec_ref(x_24);
 x_55 = lean_box(0);
}
x_74 = lean_array_get_size(x_51);
x_75 = lean_nat_dec_lt(x_2, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
x_56 = x_51;
goto block_73;
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_array_fget(x_51, x_2);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_76, 13);
x_79 = lean_ctor_get(x_76, 14);
x_80 = lean_box(0);
x_81 = lean_array_fset(x_51, x_2, x_80);
lean_inc_ref(x_1);
x_82 = l_Lean_PersistentArray_push___redArg(x_78, x_1);
lean_inc(x_26);
lean_inc_ref(x_1);
x_83 = l_Lean_PersistentHashMap_insert___redArg(x_18, x_19, x_79, x_1, x_26);
lean_ctor_set(x_76, 14, x_83);
lean_ctor_set(x_76, 13, x_82);
x_84 = lean_array_fset(x_81, x_2, x_76);
x_56 = x_84;
goto block_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_85 = lean_ctor_get(x_76, 0);
x_86 = lean_ctor_get(x_76, 1);
x_87 = lean_ctor_get(x_76, 2);
x_88 = lean_ctor_get(x_76, 3);
x_89 = lean_ctor_get(x_76, 4);
x_90 = lean_ctor_get(x_76, 5);
x_91 = lean_ctor_get(x_76, 6);
x_92 = lean_ctor_get(x_76, 7);
x_93 = lean_ctor_get(x_76, 8);
x_94 = lean_ctor_get(x_76, 9);
x_95 = lean_ctor_get(x_76, 10);
x_96 = lean_ctor_get(x_76, 11);
x_97 = lean_ctor_get(x_76, 12);
x_98 = lean_ctor_get(x_76, 13);
x_99 = lean_ctor_get(x_76, 14);
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
lean_dec(x_76);
x_100 = lean_box(0);
x_101 = lean_array_fset(x_51, x_2, x_100);
lean_inc_ref(x_1);
x_102 = l_Lean_PersistentArray_push___redArg(x_98, x_1);
lean_inc(x_26);
lean_inc_ref(x_1);
x_103 = l_Lean_PersistentHashMap_insert___redArg(x_18, x_19, x_99, x_1, x_26);
x_104 = lean_alloc_ctor(0, 15, 0);
lean_ctor_set(x_104, 0, x_85);
lean_ctor_set(x_104, 1, x_86);
lean_ctor_set(x_104, 2, x_87);
lean_ctor_set(x_104, 3, x_88);
lean_ctor_set(x_104, 4, x_89);
lean_ctor_set(x_104, 5, x_90);
lean_ctor_set(x_104, 6, x_91);
lean_ctor_set(x_104, 7, x_92);
lean_ctor_set(x_104, 8, x_93);
lean_ctor_set(x_104, 9, x_94);
lean_ctor_set(x_104, 10, x_95);
lean_ctor_set(x_104, 11, x_96);
lean_ctor_set(x_104, 12, x_97);
lean_ctor_set(x_104, 13, x_102);
lean_ctor_set(x_104, 14, x_103);
x_105 = lean_array_fset(x_101, x_2, x_104);
x_56 = x_105;
goto block_73;
}
}
block_73:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(0, 7, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_52);
lean_ctor_set(x_57, 5, x_53);
lean_ctor_set(x_57, 6, x_54);
if (lean_is_scalar(x_47)) {
 x_58 = lean_alloc_ctor(0, 4, 0);
} else {
 x_58 = x_47;
}
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set(x_58, 3, x_46);
if (lean_is_scalar(x_43)) {
 x_59 = lean_alloc_ctor(0, 16, 1);
} else {
 x_59 = x_43;
}
lean_ctor_set(x_59, 0, x_27);
lean_ctor_set(x_59, 1, x_28);
lean_ctor_set(x_59, 2, x_29);
lean_ctor_set(x_59, 3, x_30);
lean_ctor_set(x_59, 4, x_31);
lean_ctor_set(x_59, 5, x_32);
lean_ctor_set(x_59, 6, x_33);
lean_ctor_set(x_59, 7, x_34);
lean_ctor_set(x_59, 8, x_36);
lean_ctor_set(x_59, 9, x_37);
lean_ctor_set(x_59, 10, x_38);
lean_ctor_set(x_59, 11, x_39);
lean_ctor_set(x_59, 12, x_40);
lean_ctor_set(x_59, 13, x_41);
lean_ctor_set(x_59, 14, x_58);
lean_ctor_set(x_59, 15, x_42);
lean_ctor_set_uint8(x_59, sizeof(void*)*16, x_35);
x_60 = lean_st_ref_set(x_3, x_59, x_25);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc_ref(x_1);
x_62 = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_61);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
lean_ctor_set(x_64, 0, x_26);
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_26);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_26);
x_69 = !lean_is_exclusive(x_64);
if (x_69 == 0)
{
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 0);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_64);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_106; 
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_20, 0);
lean_inc(x_106);
lean_dec_ref(x_20);
lean_ctor_set(x_12, 0, x_106);
return x_12;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_12, 0);
x_108 = lean_ctor_get(x_12, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_12);
x_109 = lean_ctor_get(x_107, 13);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_107, 14);
lean_inc_ref(x_110);
lean_dec(x_107);
x_111 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0;
x_112 = l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1;
lean_inc_ref(x_1);
x_113 = l_Lean_PersistentHashMap_find_x3f___redArg(x_111, x_112, x_110, x_1);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_166; uint8_t x_167; 
x_114 = lean_st_ref_take(x_3, x_108);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 14);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_116, 2);
lean_inc_ref(x_117);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec_ref(x_114);
x_119 = lean_ctor_get(x_109, 2);
lean_inc(x_119);
lean_dec_ref(x_109);
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_115, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_115, 3);
lean_inc_ref(x_123);
x_124 = lean_ctor_get(x_115, 4);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_115, 5);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_115, 6);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_115, 7);
lean_inc_ref(x_127);
x_128 = lean_ctor_get_uint8(x_115, sizeof(void*)*16);
x_129 = lean_ctor_get(x_115, 8);
lean_inc(x_129);
x_130 = lean_ctor_get(x_115, 9);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_115, 10);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_115, 11);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_115, 12);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_115, 13);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_115, 15);
lean_inc_ref(x_135);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 lean_ctor_release(x_115, 5);
 lean_ctor_release(x_115, 6);
 lean_ctor_release(x_115, 7);
 lean_ctor_release(x_115, 8);
 lean_ctor_release(x_115, 9);
 lean_ctor_release(x_115, 10);
 lean_ctor_release(x_115, 11);
 lean_ctor_release(x_115, 12);
 lean_ctor_release(x_115, 13);
 lean_ctor_release(x_115, 14);
 lean_ctor_release(x_115, 15);
 x_136 = x_115;
} else {
 lean_dec_ref(x_115);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_116, 0);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_116, 3);
lean_inc_ref(x_139);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 lean_ctor_release(x_116, 2);
 lean_ctor_release(x_116, 3);
 x_140 = x_116;
} else {
 lean_dec_ref(x_116);
 x_140 = lean_box(0);
}
x_141 = lean_ctor_get(x_117, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_117, 1);
lean_inc_ref(x_142);
x_143 = lean_ctor_get(x_117, 2);
lean_inc_ref(x_143);
x_144 = lean_ctor_get(x_117, 3);
lean_inc_ref(x_144);
x_145 = lean_ctor_get(x_117, 4);
lean_inc_ref(x_145);
x_146 = lean_ctor_get(x_117, 5);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_117, 6);
lean_inc(x_147);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 lean_ctor_release(x_117, 4);
 lean_ctor_release(x_117, 5);
 lean_ctor_release(x_117, 6);
 x_148 = x_117;
} else {
 lean_dec_ref(x_117);
 x_148 = lean_box(0);
}
x_166 = lean_array_get_size(x_144);
x_167 = lean_nat_dec_lt(x_2, x_166);
lean_dec(x_166);
if (x_167 == 0)
{
x_149 = x_144;
goto block_165;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_168 = lean_array_fget(x_144, x_2);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 2);
lean_inc_ref(x_171);
x_172 = lean_ctor_get(x_168, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 4);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_168, 5);
lean_inc_ref(x_174);
x_175 = lean_ctor_get(x_168, 6);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 7);
lean_inc(x_176);
x_177 = lean_ctor_get(x_168, 8);
lean_inc(x_177);
x_178 = lean_ctor_get(x_168, 9);
lean_inc(x_178);
x_179 = lean_ctor_get(x_168, 10);
lean_inc(x_179);
x_180 = lean_ctor_get(x_168, 11);
lean_inc(x_180);
x_181 = lean_ctor_get(x_168, 12);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_168, 13);
lean_inc_ref(x_182);
x_183 = lean_ctor_get(x_168, 14);
lean_inc_ref(x_183);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 lean_ctor_release(x_168, 2);
 lean_ctor_release(x_168, 3);
 lean_ctor_release(x_168, 4);
 lean_ctor_release(x_168, 5);
 lean_ctor_release(x_168, 6);
 lean_ctor_release(x_168, 7);
 lean_ctor_release(x_168, 8);
 lean_ctor_release(x_168, 9);
 lean_ctor_release(x_168, 10);
 lean_ctor_release(x_168, 11);
 lean_ctor_release(x_168, 12);
 lean_ctor_release(x_168, 13);
 lean_ctor_release(x_168, 14);
 x_184 = x_168;
} else {
 lean_dec_ref(x_168);
 x_184 = lean_box(0);
}
x_185 = lean_box(0);
x_186 = lean_array_fset(x_144, x_2, x_185);
lean_inc_ref(x_1);
x_187 = l_Lean_PersistentArray_push___redArg(x_182, x_1);
lean_inc(x_119);
lean_inc_ref(x_1);
x_188 = l_Lean_PersistentHashMap_insert___redArg(x_111, x_112, x_183, x_1, x_119);
if (lean_is_scalar(x_184)) {
 x_189 = lean_alloc_ctor(0, 15, 0);
} else {
 x_189 = x_184;
}
lean_ctor_set(x_189, 0, x_169);
lean_ctor_set(x_189, 1, x_170);
lean_ctor_set(x_189, 2, x_171);
lean_ctor_set(x_189, 3, x_172);
lean_ctor_set(x_189, 4, x_173);
lean_ctor_set(x_189, 5, x_174);
lean_ctor_set(x_189, 6, x_175);
lean_ctor_set(x_189, 7, x_176);
lean_ctor_set(x_189, 8, x_177);
lean_ctor_set(x_189, 9, x_178);
lean_ctor_set(x_189, 10, x_179);
lean_ctor_set(x_189, 11, x_180);
lean_ctor_set(x_189, 12, x_181);
lean_ctor_set(x_189, 13, x_187);
lean_ctor_set(x_189, 14, x_188);
x_190 = lean_array_fset(x_186, x_2, x_189);
x_149 = x_190;
goto block_165;
}
block_165:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 7, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_142);
lean_ctor_set(x_150, 2, x_143);
lean_ctor_set(x_150, 3, x_149);
lean_ctor_set(x_150, 4, x_145);
lean_ctor_set(x_150, 5, x_146);
lean_ctor_set(x_150, 6, x_147);
if (lean_is_scalar(x_140)) {
 x_151 = lean_alloc_ctor(0, 4, 0);
} else {
 x_151 = x_140;
}
lean_ctor_set(x_151, 0, x_137);
lean_ctor_set(x_151, 1, x_138);
lean_ctor_set(x_151, 2, x_150);
lean_ctor_set(x_151, 3, x_139);
if (lean_is_scalar(x_136)) {
 x_152 = lean_alloc_ctor(0, 16, 1);
} else {
 x_152 = x_136;
}
lean_ctor_set(x_152, 0, x_120);
lean_ctor_set(x_152, 1, x_121);
lean_ctor_set(x_152, 2, x_122);
lean_ctor_set(x_152, 3, x_123);
lean_ctor_set(x_152, 4, x_124);
lean_ctor_set(x_152, 5, x_125);
lean_ctor_set(x_152, 6, x_126);
lean_ctor_set(x_152, 7, x_127);
lean_ctor_set(x_152, 8, x_129);
lean_ctor_set(x_152, 9, x_130);
lean_ctor_set(x_152, 10, x_131);
lean_ctor_set(x_152, 11, x_132);
lean_ctor_set(x_152, 12, x_133);
lean_ctor_set(x_152, 13, x_134);
lean_ctor_set(x_152, 14, x_151);
lean_ctor_set(x_152, 15, x_135);
lean_ctor_set_uint8(x_152, sizeof(void*)*16, x_128);
x_153 = lean_st_ref_set(x_3, x_152, x_118);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec_ref(x_153);
lean_inc_ref(x_1);
x_155 = l_Lean_Meta_Grind_Arith_CommRing_setTermSemiringId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_154);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec_ref(x_155);
x_157 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_119);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_119);
x_161 = lean_ctor_get(x_157, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_163 = x_157;
} else {
 lean_dec_ref(x_157);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_109);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_113, 0);
lean_inc(x_191);
lean_dec_ref(x_113);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_108);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_193 = !lean_is_exclusive(x_12);
if (x_193 == 0)
{
return x_12;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_12, 0);
x_195 = lean_ctor_get(x_12, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_12);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
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
l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0 = _init_l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__0);
l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1 = _init_l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_mkVar___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
