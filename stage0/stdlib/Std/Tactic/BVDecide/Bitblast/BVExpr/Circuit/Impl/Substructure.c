// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
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
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1;
lean_object* l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4;
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6;
lean_object* l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7;
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5;
static lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Std_Tactic_BVDecide_BVPred_bitblast(x_1, x_5);
return x_6;
}
case 1:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get_uint8(x_2, 0);
lean_dec_ref(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
x_13 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = 1;
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_22);
return x_13;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
lean_ctor_set(x_14, 1, x_25);
return x_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_28 = x_15;
} else {
 lean_dec_ref(x_15);
 x_28 = lean_box(0);
}
x_29 = 1;
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 1, 1);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_33);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_34 = x_14;
} else {
 lean_dec_ref(x_14);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_36 = x_15;
} else {
 lean_dec_ref(x_15);
 x_36 = lean_box(0);
}
x_37 = 1;
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
if (lean_is_scalar(x_34)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_34;
}
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_13, 0);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_14, 1);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = 0;
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_46);
return x_13;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
lean_inc(x_47);
lean_dec(x_15);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
lean_ctor_set(x_14, 1, x_49);
return x_13;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_52 = x_15;
} else {
 lean_dec_ref(x_15);
 x_52 = lean_box(0);
}
x_53 = 0;
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 1, 1);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_13, 0, x_55);
return x_13;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_dec(x_13);
x_57 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_57);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_58 = x_14;
} else {
 lean_dec_ref(x_14);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_15, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_60 = x_15;
} else {
 lean_dec_ref(x_15);
 x_60 = lean_box(0);
}
x_61 = 0;
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 1, 1);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_61);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_56);
return x_64;
}
}
}
case 3:
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_66 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_2);
x_68 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_66, x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_72);
lean_dec_ref(x_69);
x_73 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_71, x_67, x_70);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_72);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_75, 0);
lean_ctor_set(x_75, 0, x_72);
switch (x_65) {
case 0:
{
lean_object* x_79; 
x_79 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_78, x_75);
lean_ctor_set(x_73, 0, x_79);
return x_73;
}
case 1:
{
lean_object* x_80; 
x_80 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_78, x_75);
lean_ctor_set(x_73, 0, x_80);
return x_73;
}
case 2:
{
lean_object* x_81; 
x_81 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_78, x_75);
lean_ctor_set(x_73, 0, x_81);
return x_73;
}
default: 
{
lean_object* x_82; 
x_82 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_78, x_75);
lean_ctor_set(x_73, 0, x_82);
return x_73;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_72, 0);
x_85 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
lean_inc(x_84);
lean_dec(x_72);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
lean_ctor_set(x_75, 0, x_86);
switch (x_65) {
case 0:
{
lean_object* x_87; 
x_87 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_83, x_75);
lean_ctor_set(x_73, 0, x_87);
return x_73;
}
case 1:
{
lean_object* x_88; 
x_88 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_83, x_75);
lean_ctor_set(x_73, 0, x_88);
return x_73;
}
case 2:
{
lean_object* x_89; 
x_89 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_83, x_75);
lean_ctor_set(x_73, 0, x_89);
return x_73;
}
default: 
{
lean_object* x_90; 
x_90 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_83, x_75);
lean_ctor_set(x_73, 0, x_90);
return x_73;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_75, 0);
x_92 = lean_ctor_get(x_75, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_75);
x_93 = lean_ctor_get(x_72, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_95 = x_72;
} else {
 lean_dec_ref(x_72);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_92);
switch (x_65) {
case 0:
{
lean_object* x_98; 
x_98 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_91, x_97);
lean_ctor_set(x_73, 0, x_98);
return x_73;
}
case 1:
{
lean_object* x_99; 
x_99 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_91, x_97);
lean_ctor_set(x_73, 0, x_99);
return x_73;
}
case 2:
{
lean_object* x_100; 
x_100 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_91, x_97);
lean_ctor_set(x_73, 0, x_100);
return x_73;
}
default: 
{
lean_object* x_101; 
x_101 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_91, x_97);
lean_ctor_set(x_73, 0, x_101);
return x_73;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_73, 0);
x_103 = lean_ctor_get(x_73, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_73);
x_104 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
x_107 = lean_ctor_get(x_72, 0);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_72, sizeof(void*)*1);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 x_109 = x_72;
} else {
 lean_dec_ref(x_72);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_108);
if (lean_is_scalar(x_106)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_106;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_105);
switch (x_65) {
case 0:
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_104, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_103);
return x_113;
}
case 1:
{
lean_object* x_114; lean_object* x_115; 
x_114 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_104, x_111);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_103);
return x_115;
}
case 2:
{
lean_object* x_116; lean_object* x_117; 
x_116 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_104, x_111);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_103);
return x_117;
}
default: 
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_104, x_111);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_103);
return x_119;
}
}
}
}
default: 
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_2);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
x_124 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_121, x_3);
x_125 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc_ref(x_126);
lean_dec_ref(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc_ref(x_128);
lean_dec_ref(x_125);
x_129 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_127, x_122, x_126);
x_130 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_131);
lean_dec_ref(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc_ref(x_133);
lean_dec_ref(x_130);
x_134 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_132, x_123, x_131);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc_ref(x_138);
lean_dec_ref(x_136);
x_139 = !lean_is_exclusive(x_128);
if (x_139 == 0)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_133);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_128, 0);
x_142 = lean_ctor_get_uint8(x_128, sizeof(void*)*1);
x_143 = lean_ctor_get(x_133, 0);
x_144 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
lean_ctor_set(x_133, 0, x_141);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_142);
lean_ctor_set(x_128, 0, x_143);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_144);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_138);
lean_ctor_set(x_2, 1, x_128);
lean_ctor_set(x_2, 0, x_133);
x_145 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_137, x_2);
lean_ctor_set(x_134, 0, x_145);
return x_134;
}
else
{
lean_object* x_146; uint8_t x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_128, 0);
x_147 = lean_ctor_get_uint8(x_128, sizeof(void*)*1);
x_148 = lean_ctor_get(x_133, 0);
x_149 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
lean_inc(x_148);
lean_dec(x_133);
x_150 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_147);
lean_ctor_set(x_128, 0, x_148);
lean_ctor_set_uint8(x_128, sizeof(void*)*1, x_149);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_138);
lean_ctor_set(x_2, 1, x_128);
lean_ctor_set(x_2, 0, x_150);
x_151 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_137, x_2);
lean_ctor_set(x_134, 0, x_151);
return x_134;
}
}
else
{
lean_object* x_152; uint8_t x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_128, 0);
x_153 = lean_ctor_get_uint8(x_128, sizeof(void*)*1);
lean_inc(x_152);
lean_dec(x_128);
x_154 = lean_ctor_get(x_133, 0);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_156 = x_133;
} else {
 lean_dec_ref(x_133);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 1, 1);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_152);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_153);
x_158 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_155);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_138);
lean_ctor_set(x_2, 1, x_158);
lean_ctor_set(x_2, 0, x_157);
x_159 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_137, x_2);
lean_ctor_set(x_134, 0, x_159);
return x_134;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_160 = lean_ctor_get(x_134, 0);
x_161 = lean_ctor_get(x_134, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_134);
x_162 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc_ref(x_163);
lean_dec_ref(x_160);
x_164 = lean_ctor_get(x_128, 0);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_128, sizeof(void*)*1);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_166 = x_128;
} else {
 lean_dec_ref(x_128);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_133, 0);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_133, sizeof(void*)*1);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_169 = x_133;
} else {
 lean_dec_ref(x_133);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 1, 1);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_165);
if (lean_is_scalar(x_166)) {
 x_171 = lean_alloc_ctor(0, 1, 1);
} else {
 x_171 = x_166;
}
lean_ctor_set(x_171, 0, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_168);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_163);
lean_ctor_set(x_2, 1, x_171);
lean_ctor_set(x_2, 0, x_170);
x_172 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_162, x_2);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_161);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_174 = lean_ctor_get(x_2, 0);
x_175 = lean_ctor_get(x_2, 1);
x_176 = lean_ctor_get(x_2, 2);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_2);
x_177 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_174, x_3);
x_178 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc_ref(x_179);
lean_dec_ref(x_177);
x_180 = lean_ctor_get(x_178, 0);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc_ref(x_181);
lean_dec_ref(x_178);
x_182 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_180, x_175, x_179);
x_183 = lean_ctor_get(x_182, 0);
lean_inc_ref(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc_ref(x_184);
lean_dec_ref(x_182);
x_185 = lean_ctor_get(x_183, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc_ref(x_186);
lean_dec_ref(x_183);
x_187 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_185, x_176, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc_ref(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc_ref(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_188, 0);
lean_inc_ref(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc_ref(x_192);
lean_dec_ref(x_188);
x_193 = lean_ctor_get(x_181, 0);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_181, sizeof(void*)*1);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 x_195 = x_181;
} else {
 lean_dec_ref(x_181);
 x_195 = lean_box(0);
}
x_196 = lean_ctor_get(x_186, 0);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_186, sizeof(void*)*1);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_198 = x_186;
} else {
 lean_dec_ref(x_186);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(0, 1, 1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set_uint8(x_199, sizeof(void*)*1, x_194);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(0, 1, 1);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_197);
x_201 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_192);
x_202 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_191, x_201);
if (lean_is_scalar(x_190)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_190;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_189);
return x_203;
}
}
}
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6;
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7;
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1;
x_4 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_3(x_6, x_17, x_15, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_21);
lean_dec_ref(x_1);
x_22 = lean_apply_3(x_5, x_19, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__5_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__0);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__1);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__2);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__3);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__4);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__5);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__6);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0___closed__7);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0);
l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0 = _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__0);
l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1 = _init_l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
