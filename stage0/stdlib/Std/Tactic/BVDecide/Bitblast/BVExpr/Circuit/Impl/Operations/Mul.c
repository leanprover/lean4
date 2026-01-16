// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_isConstant___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_20; lean_object* x_21; 
x_20 = lean_nat_dec_lt(x_7, x_3);
if (x_20 == 0)
{
lean_object* x_57; 
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_8);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_array_fget_borrowed(x_6, x_7);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_shiftr(x_58, x_59);
x_61 = lean_nat_land(x_59, x_58);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_60);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_20);
x_21 = x_64;
goto block_56;
}
else
{
uint8_t x_65; lean_object* x_66; 
x_65 = 0;
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_65);
x_21 = x_66;
goto block_56;
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_10, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_4 = x_14;
x_7 = x_17;
x_8 = x_15;
goto _start;
}
block_56:
{
uint8_t x_22; uint8_t x_23; 
x_22 = 0;
x_23 = l_Std_Sat_AIG_isConstant___redArg(x_4, x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_7);
lean_inc_ref(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_7);
x_25 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(x_3, x_4, x_24);
lean_dec_ref(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_8);
lean_ctor_set(x_25, 0, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_28 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_1, x_2, x_3, x_27, x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_28);
x_31 = lean_array_fget_borrowed(x_6, x_7);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_shiftr(x_31, x_32);
x_34 = lean_nat_land(x_32, x_31);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_20);
x_9 = x_30;
x_10 = x_29;
x_11 = x_37;
goto block_19;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_23);
x_9 = x_30;
x_10 = x_29;
x_11 = x_38;
goto block_19;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
lean_inc_ref(x_8);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_40);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_42 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_1, x_2, x_3, x_39, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_42);
x_45 = lean_array_fget_borrowed(x_6, x_7);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_shiftr(x_45, x_46);
x_48 = lean_nat_land(x_46, x_45);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_20);
x_9 = x_44;
x_10 = x_43;
x_11 = x_51;
goto block_19;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_23);
x_9 = x_44;
x_10 = x_43;
x_11 = x_52;
goto block_19;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_7, x_53);
lean_dec(x_7);
x_7 = x_54;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_5);
x_10 = l_BitVec_ofNat(x_3, x_6);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_10);
lean_dec(x_10);
x_20 = lean_array_fget_borrowed(x_9, x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_shiftr(x_20, x_21);
x_23 = lean_nat_land(x_21, x_20);
x_24 = lean_nat_dec_eq(x_23, x_6);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
x_25 = 1;
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_25);
x_12 = x_26;
goto block_19;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_7);
x_12 = x_27;
goto block_19;
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_8);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_11);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(x_1, x_2, x_3, x_15, x_8, x_9, x_17, x_16);
lean_dec_ref(x_9);
return x_18;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_5);
x_28 = l_Std_Sat_AIG_RefVec_empty(lean_box(0), x_1, x_2, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_6);
x_9 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
lean_ctor_set(x_5, 1, x_6);
lean_ctor_set(x_5, 0, x_7);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(x_1, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_6);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(x_1, x_2, x_3, x_4, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(x_1, x_2, x_3, x_4, x_5);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
