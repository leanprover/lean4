// Lean compiler output
// Module: Std.Sat.AIG.If
// Imports: Std.Sat.AIG.CachedGatesLemmas Std.Sat.AIG.LawfulVecOperator
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
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_19 = 1;
lean_ctor_set(x_10, 0, x_16);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_12, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_5, 0, x_17);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_18);
lean_ctor_set(x_21, 0, x_5);
x_24 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_23, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_5, 0, x_17);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_25, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_30);
lean_dec(x_10);
x_32 = 1;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_12, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_30);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_31);
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_36, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_5, 0);
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_42);
lean_dec(x_7);
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_46 = x_10;
} else {
 lean_dec_ref(x_10);
 x_46 = lean_box(0);
}
x_47 = 1;
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 1, 1);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_43);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_2);
lean_inc(x_1);
x_51 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_12, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_44);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_5);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_52, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_57 = lean_ctor_get(x_5, 0);
lean_inc(x_57);
lean_dec(x_5);
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_60 = x_7;
} else {
 lean_dec_ref(x_7);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_63 = x_10;
} else {
 lean_dec_ref(x_10);
 x_63 = lean_box(0);
}
x_64 = 1;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 1);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(0, 1, 1);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_12, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_61);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_62);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_69, x_73);
return x_74;
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_9, 0);
lean_inc(x_75);
lean_dec(x_9);
x_76 = !lean_is_exclusive(x_5);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_7);
if (x_77 == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_10);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_5, 0);
x_80 = lean_ctor_get(x_10, 0);
x_81 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
x_82 = 0;
lean_ctor_set(x_10, 0, x_79);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_10);
lean_ctor_set(x_83, 1, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_75, x_83);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_5, 0, x_80);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_81);
lean_ctor_set(x_84, 0, x_5);
x_87 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_86, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_84, 0);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
lean_ctor_set(x_5, 0, x_80);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_81);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_88, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_10, 0);
x_94 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
lean_inc(x_93);
lean_dec(x_10);
x_95 = 0;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_98 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_75, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
 x_101 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_93);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_94);
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_5);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_99, x_102);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_ctor_get(x_5, 0);
x_105 = lean_ctor_get(x_7, 0);
x_106 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
lean_inc(x_105);
lean_dec(x_7);
x_107 = lean_ctor_get(x_10, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_109 = x_10;
} else {
 lean_dec_ref(x_10);
 x_109 = lean_box(0);
}
x_110 = 0;
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 1, 1);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_104);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_112, 0, x_105);
lean_ctor_set_uint8(x_112, sizeof(void*)*1, x_106);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
lean_inc(x_2);
lean_inc(x_1);
x_114 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_75, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_107);
lean_ctor_set_uint8(x_5, sizeof(void*)*1, x_108);
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_5);
lean_ctor_set(x_118, 1, x_116);
x_119 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_115, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_120 = lean_ctor_get(x_5, 0);
lean_inc(x_120);
lean_dec(x_5);
x_121 = lean_ctor_get(x_7, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_123 = x_7;
} else {
 lean_dec_ref(x_7);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_10, 0);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_10, sizeof(void*)*1);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_126 = x_10;
} else {
 lean_dec_ref(x_10);
 x_126 = lean_box(0);
}
x_127 = 0;
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 1, 1);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_127);
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(0, 1, 1);
} else {
 x_129 = x_123;
}
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*1, x_122);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
lean_inc(x_2);
lean_inc(x_1);
x_131 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_75, x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_135, 0, x_124);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_125);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
x_137 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_132, x_136);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkIfCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_mkIfCached___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_5, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
x_17 = lean_array_fget(x_8, x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_21);
x_22 = lean_array_fget(x_9, x_5);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_26);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_4, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_14);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
x_35 = lean_box(x_34);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_33);
x_36 = lean_array_push(x_10, x_22);
x_4 = x_30;
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_32;
x_10 = x_36;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_41);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_7);
lean_ctor_set(x_42, 1, x_20);
lean_ctor_set(x_42, 2, x_40);
lean_inc(x_2);
lean_inc(x_1);
x_43 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_4, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_13);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_14);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_push(x_10, x_50);
x_4 = x_44;
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_46;
x_10 = x_51;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_ite_go___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Sat_AIG_RefVec_ite_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_mk_empty_array_with_capacity(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Std_Sat_AIG_RefVec_ite_go___rarg(x_1, x_2, x_3, x_4, x_10, lean_box(0), x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Sat_AIG_RefVec_ite___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_RefVec_ite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
