// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Circuit
// Imports: Std.Sat.AIG.CachedGates Std.Sat.AIG.CachedGatesLemmas Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic Std.Sat.AIG.If
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
lean_object* l_Std_Sat_AIG_mkXorCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkIfCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_empty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go(lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_6, x_4, x_8);
return x_9;
}
case 1:
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
x_11 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_4, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_12, x_6, lean_box(0));
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = 1;
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
lean_ctor_set(x_13, 1, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_25 = x_14;
} else {
 lean_dec_ref(x_14);
 x_25 = lean_box(0);
}
x_26 = 1;
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 1, 1);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_13, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_32);
return x_13;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
lean_inc(x_33);
lean_dec(x_14);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
lean_ctor_set(x_13, 1, x_35);
return x_13;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_13, 0);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_38 = x_14;
} else {
 lean_dec_ref(x_14);
 x_38 = lean_box(0);
}
x_39 = 0;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 1);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
case 3:
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_43 = lean_ctor_get(x_5, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_43, x_6, lean_box(0));
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_46, x_44, x_6, lean_box(0));
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_48, 0, x_47);
switch (x_42) {
case 0:
{
lean_object* x_52; 
x_52 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_51, x_48);
return x_52;
}
case 1:
{
lean_object* x_53; 
x_53 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_51, x_48);
return x_53;
}
case 2:
{
lean_object* x_54; 
x_54 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_51, x_48);
return x_54;
}
default: 
{
lean_object* x_55; 
x_55 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_51, x_48);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_48, 0);
x_57 = lean_ctor_get(x_47, 0);
x_58 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_inc(x_57);
lean_dec(x_47);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_58);
lean_ctor_set(x_48, 0, x_59);
switch (x_42) {
case 0:
{
lean_object* x_60; 
x_60 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_56, x_48);
return x_60;
}
case 1:
{
lean_object* x_61; 
x_61 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_56, x_48);
return x_61;
}
case 2:
{
lean_object* x_62; 
x_62 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_56, x_48);
return x_62;
}
default: 
{
lean_object* x_63; 
x_63 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_56, x_48);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_48, 0);
x_65 = lean_ctor_get(x_48, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_48);
x_66 = lean_ctor_get(x_47, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_68 = x_47;
} else {
 lean_dec_ref(x_47);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 1, 1);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
switch (x_42) {
case 0:
{
lean_object* x_71; 
x_71 = l_Std_Sat_AIG_mkGateCached___rarg(x_1, x_2, x_64, x_70);
return x_71;
}
case 1:
{
lean_object* x_72; 
x_72 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_64, x_70);
return x_72;
}
case 2:
{
lean_object* x_73; 
x_73 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_64, x_70);
return x_73;
}
default: 
{
lean_object* x_74; 
x_74 = l_Std_Sat_AIG_mkOrCached___rarg(x_1, x_2, x_64, x_70);
return x_74;
}
}
}
}
default: 
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_5);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_76 = lean_ctor_get(x_5, 0);
x_77 = lean_ctor_get(x_5, 1);
x_78 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_79 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_76, x_6, lean_box(0));
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_80, x_77, x_6, lean_box(0));
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_2);
lean_inc(x_1);
x_85 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_83, x_78, x_6, lean_box(0));
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
lean_object* x_90; 
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 2, x_87);
lean_ctor_set(x_5, 1, x_84);
lean_ctor_set(x_5, 0, x_81);
x_90 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_86, x_5);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_84, 0);
x_92 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
lean_inc(x_91);
lean_dec(x_84);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 2, x_87);
lean_ctor_set(x_5, 1, x_93);
lean_ctor_set(x_5, 0, x_81);
x_94 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_86, x_5);
return x_94;
}
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_81, 0);
x_96 = lean_ctor_get_uint8(x_81, sizeof(void*)*1);
lean_inc(x_95);
lean_dec(x_81);
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_100 = x_84;
} else {
 lean_dec_ref(x_84);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(0, 1, 1);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_99);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 2, x_87);
lean_ctor_set(x_5, 1, x_101);
lean_ctor_set(x_5, 0, x_97);
x_102 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_86, x_5);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_103 = lean_ctor_get(x_5, 0);
x_104 = lean_ctor_get(x_5, 1);
x_105 = lean_ctor_get(x_5, 2);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_106 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_103, x_6, lean_box(0));
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_109 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_107, x_104, x_6, lean_box(0));
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_2);
lean_inc(x_1);
x_112 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_110, x_105, x_6, lean_box(0));
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_108, sizeof(void*)*1);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 1, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_116);
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
x_120 = lean_ctor_get_uint8(x_111, sizeof(void*)*1);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_121 = x_111;
} else {
 lean_dec_ref(x_111);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 1, 1);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set_uint8(x_122, sizeof(void*)*1, x_120);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_118);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_114);
x_124 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_113, x_123);
return x_124;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Sat_AIG_empty___rarg(x_1, x_2);
x_8 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_7, x_4, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_ofBoolExprCached___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_3(x_6, x_17, x_15, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_3(x_5, x_19, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg), 6, 0);
return x_3;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
