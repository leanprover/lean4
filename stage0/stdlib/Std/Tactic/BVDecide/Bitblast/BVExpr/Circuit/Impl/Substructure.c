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
lean_dec(x_2);
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
lean_dec(x_2);
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
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
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
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(1);
x_23 = lean_unbox(x_22);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
lean_ctor_set(x_14, 1, x_26);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_30 = x_15;
} else {
 lean_dec_ref(x_15);
 x_30 = lean_box(0);
}
x_31 = lean_box(1);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 1, 1);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_29);
x_33 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_37 = x_14;
} else {
 lean_dec_ref(x_14);
 x_37 = lean_box(0);
}
x_38 = lean_ctor_get(x_15, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_39 = x_15;
} else {
 lean_dec_ref(x_15);
 x_39 = lean_box(0);
}
x_40 = lean_box(1);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 1, 1);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_14, 1);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_box(0);
x_51 = lean_unbox(x_50);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_51);
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
lean_ctor_set(x_14, 1, x_54);
return x_13;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
x_57 = lean_ctor_get(x_15, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_58 = x_15;
} else {
 lean_dec_ref(x_15);
 x_58 = lean_box(0);
}
x_59 = lean_box(0);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 1, 1);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_57);
x_61 = lean_unbox(x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_61);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_13, 0, x_62);
return x_13;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_dec(x_13);
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_65 = x_14;
} else {
 lean_dec_ref(x_14);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_15, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_67 = x_15;
} else {
 lean_dec_ref(x_15);
 x_67 = lean_box(0);
}
x_68 = lean_box(0);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 1, 1);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_66);
x_70 = lean_unbox(x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*1, x_70);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_63);
return x_72;
}
}
}
case 3:
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_74, x_3);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_79, x_75, x_78);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_80);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_83, 0);
lean_ctor_set(x_83, 0, x_80);
switch (x_73) {
case 0:
{
lean_object* x_87; 
x_87 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_86, x_83);
lean_ctor_set(x_81, 0, x_87);
return x_81;
}
case 1:
{
lean_object* x_88; 
x_88 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_86, x_83);
lean_ctor_set(x_81, 0, x_88);
return x_81;
}
case 2:
{
lean_object* x_89; 
x_89 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_86, x_83);
lean_ctor_set(x_81, 0, x_89);
return x_81;
}
default: 
{
lean_object* x_90; 
x_90 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_86, x_83);
lean_ctor_set(x_81, 0, x_90);
return x_81;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_83, 0);
x_92 = lean_ctor_get(x_80, 0);
x_93 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_inc(x_92);
lean_dec(x_80);
x_94 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*1, x_93);
lean_ctor_set(x_83, 0, x_94);
switch (x_73) {
case 0:
{
lean_object* x_95; 
x_95 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_91, x_83);
lean_ctor_set(x_81, 0, x_95);
return x_81;
}
case 1:
{
lean_object* x_96; 
x_96 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_91, x_83);
lean_ctor_set(x_81, 0, x_96);
return x_81;
}
case 2:
{
lean_object* x_97; 
x_97 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_91, x_83);
lean_ctor_set(x_81, 0, x_97);
return x_81;
}
default: 
{
lean_object* x_98; 
x_98 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_91, x_83);
lean_ctor_set(x_81, 0, x_98);
return x_81;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_83, 0);
x_100 = lean_ctor_get(x_83, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_83);
x_101 = lean_ctor_get(x_80, 0);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_103 = x_80;
} else {
 lean_dec_ref(x_80);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 1, 1);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
switch (x_73) {
case 0:
{
lean_object* x_106; 
x_106 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_99, x_105);
lean_ctor_set(x_81, 0, x_106);
return x_81;
}
case 1:
{
lean_object* x_107; 
x_107 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_99, x_105);
lean_ctor_set(x_81, 0, x_107);
return x_81;
}
case 2:
{
lean_object* x_108; 
x_108 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_99, x_105);
lean_ctor_set(x_81, 0, x_108);
return x_81;
}
default: 
{
lean_object* x_109; 
x_109 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_99, x_105);
lean_ctor_set(x_81, 0, x_109);
return x_81;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_110 = lean_ctor_get(x_81, 0);
x_111 = lean_ctor_get(x_81, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_81);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_80, 0);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_117 = x_80;
} else {
 lean_dec_ref(x_80);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 1, 1);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_116);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
switch (x_73) {
case 0:
{
lean_object* x_120; lean_object* x_121; 
x_120 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_112, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_111);
return x_121;
}
case 1:
{
lean_object* x_122; lean_object* x_123; 
x_122 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_112, x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_111);
return x_123;
}
case 2:
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_112, x_119);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_111);
return x_125;
}
default: 
{
lean_object* x_126; lean_object* x_127; 
x_126 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_112, x_119);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_111);
return x_127;
}
}
}
}
default: 
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_2);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_129 = lean_ctor_get(x_2, 0);
x_130 = lean_ctor_get(x_2, 1);
x_131 = lean_ctor_get(x_2, 2);
x_132 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_129, x_3);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
lean_dec(x_133);
x_137 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_135, x_130, x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_140, x_131, x_139);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = !lean_is_exclusive(x_136);
if (x_147 == 0)
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_141);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_136, 0);
x_150 = lean_ctor_get_uint8(x_136, sizeof(void*)*1);
x_151 = lean_ctor_get(x_141, 0);
x_152 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_ctor_set(x_141, 0, x_149);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_150);
lean_ctor_set(x_136, 0, x_151);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_152);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_146);
lean_ctor_set(x_2, 1, x_136);
lean_ctor_set(x_2, 0, x_141);
x_153 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_145, x_2);
lean_ctor_set(x_142, 0, x_153);
return x_142;
}
else
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_136, 0);
x_155 = lean_ctor_get_uint8(x_136, sizeof(void*)*1);
x_156 = lean_ctor_get(x_141, 0);
x_157 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
lean_inc(x_156);
lean_dec(x_141);
x_158 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*1, x_155);
lean_ctor_set(x_136, 0, x_156);
lean_ctor_set_uint8(x_136, sizeof(void*)*1, x_157);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_146);
lean_ctor_set(x_2, 1, x_136);
lean_ctor_set(x_2, 0, x_158);
x_159 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_145, x_2);
lean_ctor_set(x_142, 0, x_159);
return x_142;
}
}
else
{
lean_object* x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_136, 0);
x_161 = lean_ctor_get_uint8(x_136, sizeof(void*)*1);
lean_inc(x_160);
lean_dec(x_136);
x_162 = lean_ctor_get(x_141, 0);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_164 = x_141;
} else {
 lean_dec_ref(x_141);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 1, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_161);
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_162);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_163);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_146);
lean_ctor_set(x_2, 1, x_166);
lean_ctor_set(x_2, 0, x_165);
x_167 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_145, x_2);
lean_ctor_set(x_142, 0, x_167);
return x_142;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_168 = lean_ctor_get(x_142, 0);
x_169 = lean_ctor_get(x_142, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_142);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_136, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_136, sizeof(void*)*1);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_174 = x_136;
} else {
 lean_dec_ref(x_136);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_141, 0);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_141, sizeof(void*)*1);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_177 = x_141;
} else {
 lean_dec_ref(x_141);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(0, 1, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_173);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 1, 1);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set_uint8(x_179, sizeof(void*)*1, x_176);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_171);
lean_ctor_set(x_2, 1, x_179);
lean_ctor_set(x_2, 0, x_178);
x_180 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_170, x_2);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_169);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_182 = lean_ctor_get(x_2, 0);
x_183 = lean_ctor_get(x_2, 1);
x_184 = lean_ctor_get(x_2, 2);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_2);
x_185 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_182, x_3);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_ctor_get(x_186, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_188, x_183, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_195 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_193, x_184, x_192);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_dec(x_196);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_189, sizeof(void*)*1);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_203 = x_189;
} else {
 lean_dec_ref(x_189);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_194, sizeof(void*)*1);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 x_206 = x_194;
} else {
 lean_dec_ref(x_194);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 1, 1);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_201);
lean_ctor_set_uint8(x_207, sizeof(void*)*1, x_202);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 1, 1);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_204);
lean_ctor_set_uint8(x_208, sizeof(void*)*1, x_205);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set(x_209, 2, x_200);
x_210 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_199, x_209);
if (lean_is_scalar(x_198)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_198;
}
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_197);
return x_211;
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
lean_inc(x_5);
lean_dec(x_4);
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
