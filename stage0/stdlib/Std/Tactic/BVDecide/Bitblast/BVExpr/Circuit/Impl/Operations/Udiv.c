// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Sat.AIG.If
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec_ref(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_mul(x_7, x_12);
lean_dec(x_7);
x_14 = l_Bool_toNat(x_8);
x_15 = lean_nat_lor(x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_array_push(x_11, x_15);
x_17 = lean_nat_add(x_9, x_1);
x_18 = l_Array_append___redArg(x_16, x_6);
lean_dec_ref(x_6);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_3, 1);
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_20, sizeof(void*)*1);
lean_dec_ref(x_20);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = lean_mk_empty_array_with_capacity(x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_nat_mul(x_22, x_27);
lean_dec(x_22);
x_29 = l_Bool_toNat(x_23);
x_30 = lean_nat_lor(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_array_push(x_26, x_30);
x_32 = lean_nat_add(x_24, x_1);
x_33 = l_Array_append___redArg(x_31, x_21);
lean_dec_ref(x_21);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(x_1, x_2, x_34);
lean_dec_ref(x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_140; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
x_13 = lean_nat_add(x_8, x_11);
x_14 = 0;
x_140 = lean_nat_dec_lt(x_12, x_3);
if (x_140 == 0)
{
lean_object* x_141; 
x_141 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
x_15 = x_141;
goto block_139;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_142 = lean_array_fget_borrowed(x_5, x_12);
x_143 = lean_nat_shiftr(x_142, x_11);
x_144 = lean_nat_land(x_11, x_142);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_nat_dec_eq(x_144, x_145);
lean_dec(x_144);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_140);
x_15 = x_147;
goto block_139;
}
else
{
lean_object* x_148; 
x_148 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set_uint8(x_148, sizeof(void*)*1, x_14);
x_15 = x_148;
goto block_139;
}
}
block_139:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
lean_inc_ref(x_9);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_9);
x_22 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_19, x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1;
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_9);
x_27 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_24, x_22);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_20);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 0, x_20);
lean_inc_ref(x_27);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_31 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(x_1, x_2, x_3, x_29, x_27);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_31);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_34 = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(x_1, x_2, x_3, x_32, x_27);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_34);
lean_inc_ref(x_36);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_30);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_38 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_35, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc_ref(x_40);
lean_dec_ref(x_38);
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_20);
lean_ctor_set(x_42, 2, x_33);
x_43 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_39, x_42);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 2, x_13);
lean_ctor_set(x_46, 3, x_40);
lean_ctor_set(x_46, 4, x_45);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_20);
lean_ctor_set(x_50, 2, x_33);
x_51 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_39, x_50);
lean_dec(x_3);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc_ref(x_53);
lean_dec_ref(x_51);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_12);
lean_ctor_set(x_54, 2, x_13);
lean_ctor_set(x_54, 3, x_40);
lean_ctor_set(x_54, 4, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_27, 0);
x_56 = lean_ctor_get(x_27, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_27);
lean_inc_ref(x_20);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_20);
lean_ctor_set(x_57, 1, x_6);
lean_inc_ref(x_57);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_58 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(x_1, x_2, x_3, x_55, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_58);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_61 = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(x_1, x_2, x_3, x_59, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
lean_dec_ref(x_61);
lean_inc_ref(x_63);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_25);
lean_ctor_set(x_64, 2, x_56);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_65 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_62, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc_ref(x_67);
lean_dec_ref(x_65);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_63, sizeof(void*)*1);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_70 = x_63;
} else {
 lean_dec_ref(x_63);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 1);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_69);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_20);
lean_ctor_set(x_72, 2, x_60);
x_73 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_66, x_72);
lean_dec(x_3);
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc_ref(x_75);
lean_dec_ref(x_73);
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_12);
lean_ctor_set(x_76, 2, x_13);
lean_ctor_set(x_76, 3, x_67);
lean_ctor_set(x_76, 4, x_75);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_77 = lean_ctor_get(x_22, 0);
x_78 = lean_ctor_get(x_22, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_22);
x_79 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_9);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_77, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc_ref(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
lean_inc_ref(x_20);
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_6);
lean_inc_ref(x_85);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_86 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(x_1, x_2, x_3, x_82, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc_ref(x_88);
lean_dec_ref(x_86);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_89 = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(x_1, x_2, x_3, x_87, x_85);
x_90 = lean_ctor_get(x_89, 0);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc_ref(x_91);
lean_dec_ref(x_89);
lean_inc_ref(x_91);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
lean_ctor_set(x_92, 2, x_83);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_93 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_90, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc_ref(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_91, 0);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_91, sizeof(void*)*1);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_98 = x_91;
} else {
 lean_dec_ref(x_91);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(0, 1, 1);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_97);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_20);
lean_ctor_set(x_100, 2, x_88);
x_101 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_94, x_100);
lean_dec(x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc_ref(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc_ref(x_103);
lean_dec_ref(x_101);
x_104 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_12);
lean_ctor_set(x_104, 2, x_13);
lean_ctor_set(x_104, 3, x_95);
lean_ctor_set(x_104, 4, x_103);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_105 = lean_ctor_get(x_17, 0);
x_106 = lean_ctor_get(x_17, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_17);
x_107 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
lean_inc_ref(x_9);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_9);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_105, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc_ref(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc_ref(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_9);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(x_3, x_110, x_114);
x_116 = lean_ctor_get(x_115, 0);
lean_inc_ref(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc_ref(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
lean_inc_ref(x_106);
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_106);
lean_ctor_set(x_119, 1, x_6);
lean_inc_ref(x_119);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_120 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(x_1, x_2, x_3, x_116, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc_ref(x_122);
lean_dec_ref(x_120);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_123 = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(x_1, x_2, x_3, x_121, x_119);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc_ref(x_125);
lean_dec_ref(x_123);
lean_inc_ref(x_125);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_111);
lean_ctor_set(x_126, 2, x_117);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_127 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_124, x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc_ref(x_129);
lean_dec_ref(x_127);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_132 = x_125;
} else {
 lean_dec_ref(x_125);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 1, 1);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set_uint8(x_133, sizeof(void*)*1, x_131);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_106);
lean_ctor_set(x_134, 2, x_122);
x_135 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_128, x_134);
lean_dec(x_3);
x_136 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc_ref(x_137);
lean_dec_ref(x_135);
x_138 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_12);
lean_ctor_set(x_138, 2, x_13);
lean_ctor_set(x_138, 3, x_129);
lean_ctor_set(x_138, 4, x_137);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 1)
{
lean_object* x_14; 
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_7);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 3);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_15, 4);
lean_inc_ref(x_20);
lean_dec_ref(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_5, x_21);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_16, x_22, x_6, x_7, x_17, x_18, x_19, x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_BitVec_ofNat(x_3, x_9);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_10);
lean_dec(x_10);
lean_inc_ref(x_11);
lean_inc_ref(x_8);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
lean_inc_ref_n(x_11, 2);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_13, x_3, x_7, x_8, x_3, x_9, x_11, x_11);
lean_dec_ref(x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_15, 2);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; 
lean_ctor_set(x_15, 2, x_18);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 0, x_14);
x_21 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_17, x_15);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
lean_ctor_set(x_15, 2, x_18);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 0, x_24);
x_25 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_17, x_15);
lean_dec(x_3);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_30 = x_14;
} else {
 lean_dec_ref(x_14);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 1, 1);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_29);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_27);
x_33 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_26, x_32);
lean_dec(x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_BitVec_ofNat(x_3, x_36);
x_38 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_37);
lean_dec(x_37);
lean_inc_ref(x_38);
lean_inc_ref(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_40 = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(x_1, x_2, x_3, x_4, x_39);
lean_dec_ref(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_40);
lean_inc_ref_n(x_38, 2);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_43 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_41, x_3, x_34, x_35, x_3, x_36, x_38, x_38);
lean_dec_ref(x_34);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc_ref(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 lean_ctor_release(x_43, 2);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 1, 1);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_48);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 3, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
lean_ctor_set(x_51, 2, x_45);
x_52 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_44, x_51);
lean_dec(x_3);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_If(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
