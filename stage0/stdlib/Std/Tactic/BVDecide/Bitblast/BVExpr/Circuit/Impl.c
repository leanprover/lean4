// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred Std.Tactic.BVDecide.Bitblast.BoolExpr.Circuit
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
lean_object* l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object*, uint8_t);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2;
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__1(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__5;
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(lean_object*, lean_object*);
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1;
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Std_Tactic_BVDecide_BVPred_bitblast(x_1, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_ctor_get_uint8(x_2, 0);
lean_dec(x_2);
x_6 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 1;
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 1;
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_16);
lean_ctor_set(x_8, 1, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
x_21 = 1;
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 1, 1);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_8, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = 0;
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_27);
return x_8;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
x_29 = 0;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
lean_ctor_set(x_8, 1, x_30);
return x_8;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_33 = x_9;
} else {
 lean_dec_ref(x_9);
 x_33 = lean_box(0);
}
x_34 = 0;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 1);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
case 3:
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_38 = lean_ctor_get(x_2, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_dec(x_2);
x_40 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_41, x_39);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_43, 0);
lean_ctor_set(x_43, 0, x_42);
switch (x_37) {
case 0:
{
lean_object* x_47; 
x_47 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_46, x_43);
return x_47;
}
case 1:
{
lean_object* x_48; 
x_48 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_46, x_43);
return x_48;
}
case 2:
{
lean_object* x_49; 
x_49 = l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_46, x_43);
return x_49;
}
default: 
{
lean_object* x_50; 
x_50 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_46, x_43);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_inc(x_52);
lean_dec(x_42);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
lean_ctor_set(x_43, 0, x_54);
switch (x_37) {
case 0:
{
lean_object* x_55; 
x_55 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_51, x_43);
return x_55;
}
case 1:
{
lean_object* x_56; 
x_56 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_51, x_43);
return x_56;
}
case 2:
{
lean_object* x_57; 
x_57 = l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_51, x_43);
return x_57;
}
default: 
{
lean_object* x_58; 
x_58 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_51, x_43);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_43, 0);
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_43);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_63 = x_42;
} else {
 lean_dec_ref(x_42);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 1);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
switch (x_37) {
case 0:
{
lean_object* x_66; 
x_66 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_59, x_65);
return x_66;
}
case 1:
{
lean_object* x_67; 
x_67 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__19(x_59, x_65);
return x_67;
}
case 2:
{
lean_object* x_68; 
x_68 = l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_59, x_65);
return x_68;
}
default: 
{
lean_object* x_69; 
x_69 = l_Std_Sat_AIG_mkOrCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__24(x_59, x_65);
return x_69;
}
}
}
}
default: 
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_2);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
x_73 = lean_ctor_get(x_2, 2);
x_74 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_75, x_72);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_78, x_73);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = !lean_is_exclusive(x_76);
if (x_83 == 0)
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_79);
if (x_84 == 0)
{
lean_object* x_85; 
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_82);
lean_ctor_set(x_2, 1, x_79);
lean_ctor_set(x_2, 0, x_76);
x_85 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_81, x_2);
return x_85;
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_82);
lean_ctor_set(x_2, 1, x_88);
lean_ctor_set(x_2, 0, x_76);
x_89 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_81, x_2);
return x_89;
}
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_ctor_get(x_76, 0);
x_91 = lean_ctor_get_uint8(x_76, sizeof(void*)*1);
lean_inc(x_90);
lean_dec(x_76);
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_ctor_get(x_79, 0);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_95 = x_79;
} else {
 lean_dec_ref(x_79);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(0, 1, 1);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_94);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_82);
lean_ctor_set(x_2, 1, x_96);
lean_ctor_set(x_2, 0, x_92);
x_97 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_81, x_2);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_98 = lean_ctor_get(x_2, 0);
x_99 = lean_ctor_get(x_2, 1);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_2);
x_101 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1, x_98);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_102, x_99);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_105, x_100);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get_uint8(x_103, sizeof(void*)*1);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(0, 1, 1);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_111);
x_114 = lean_ctor_get(x_106, 0);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_106, sizeof(void*)*1);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 1, 1);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_115);
x_118 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_118, 2, x_109);
x_119 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__27(x_108, x_118);
return x_119;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2;
x_3 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2;
x_3 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__3);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__4);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__5 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__5();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__5);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__6);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
