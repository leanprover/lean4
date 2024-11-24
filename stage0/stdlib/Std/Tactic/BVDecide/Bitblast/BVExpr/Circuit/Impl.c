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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2;
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(lean_object*, uint8_t);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__5(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1;
lean_object* l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2;
lean_object* l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2;
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1;
lean_object* l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__1(lean_object*);
lean_object* l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(lean_object*, lean_object*);
static lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___boxed(lean_object*);
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3;
return x_2;
}
}
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1;
x_2 = l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = 0;
x_7 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = 1;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_7);
x_10 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_11, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_6);
x_17 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_8);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_14, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = 0;
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_1, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_28, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_22);
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_24);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_Sat_AIG_mkGateCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__21(x_31, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__4(x_1, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_Sat_AIG_mkNotCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__30(x_9, x_10);
return x_11;
}
case 3:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_1, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_16, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_18, 0, x_17);
switch (x_12) {
case 0:
{
lean_object* x_21; 
x_21 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_20, x_18);
return x_21;
}
case 1:
{
lean_object* x_22; 
x_22 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_20, x_18);
return x_22;
}
case 2:
{
lean_object* x_23; 
x_23 = l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_20, x_18);
return x_23;
}
default: 
{
lean_object* x_24; 
x_24 = l_Std_Sat_AIG_mkImpCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__5(x_20, x_18);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
switch (x_12) {
case 0:
{
lean_object* x_28; 
x_28 = l_Std_Sat_AIG_mkAndCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__25(x_25, x_27);
return x_28;
}
case 1:
{
lean_object* x_29; 
x_29 = l_Std_Sat_AIG_mkXorCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__20(x_25, x_27);
return x_29;
}
case 2:
{
lean_object* x_30; 
x_30 = l_Std_Sat_AIG_mkBEqCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__9(x_25, x_27);
return x_30;
}
default: 
{
lean_object* x_31; 
x_31 = l_Std_Sat_AIG_mkImpCached___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__5(x_25, x_27);
return x_31;
}
}
}
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_1, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_37, x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_40, x_35);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_44);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_38);
x_45 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_43, x_2);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 1);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_49 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_1, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_50, x_47);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_53, x_48);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_57);
x_59 = l_Std_Sat_AIG_mkIfCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__29(x_56, x_58);
return x_59;
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
x_3 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2;
x_3 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__4(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3(x_1);
lean_dec(x_1);
return x_2;
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
l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1 = _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__1);
l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2 = _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2();
lean_mark_persistent(l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__2);
l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3 = _init_l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3();
lean_mark_persistent(l_Std_Sat_AIG_Cache_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__3___closed__3);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__1);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2___closed__2);
l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2 = _init_l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2();
lean_mark_persistent(l_Std_Sat_AIG_empty___at_Std_Tactic_BVDecide_BVLogicalExpr_bitblast___spec__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
