// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_countKnown_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Sat_AIG_isConstant___rarg(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_7, x_3);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_array_fget(x_6, x_7);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_nat_div(x_70, x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_land(x_73, x_70);
lean_dec(x_70);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_eq(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
uint8_t x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; 
x_77 = 1;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = 0;
x_80 = l_Std_Sat_AIG_isConstant___rarg(x_4, x_78, x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_11 = x_81;
goto block_69;
}
else
{
lean_object* x_82; 
x_82 = lean_nat_add(x_7, x_73);
lean_dec(x_7);
x_7 = x_82;
goto _start;
}
}
else
{
uint8_t x_84; lean_object* x_85; uint8_t x_86; 
x_84 = 0;
x_85 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_85, 0, x_72);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_84);
x_86 = l_Std_Sat_AIG_isConstant___rarg(x_4, x_85, x_84);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_box(0);
x_11 = x_87;
goto block_69;
}
else
{
lean_object* x_88; 
x_88 = lean_nat_add(x_7, x_73);
lean_dec(x_7);
x_7 = x_88;
goto _start;
}
}
block_69:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_7);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___rarg(x_1, x_2, x_3, x_4, x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_8);
lean_ctor_set(x_13, 0, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___rarg(x_1, x_2, x_3, x_15, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_fget(x_6, x_7);
x_20 = lean_unsigned_to_nat(2u);
x_21 = lean_nat_div(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_land(x_22, x_19);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
x_26 = lean_nat_add(x_7, x_22);
lean_dec(x_7);
if (x_25 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = 1;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
lean_ctor_set(x_29, 2, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_17, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_4 = x_31;
x_7 = x_26;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_17, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_4 = x_38;
x_7 = x_26;
x_8 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
lean_inc(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___rarg(x_1, x_2, x_3, x_41, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_array_fget(x_6, x_7);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_div(x_47, x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_land(x_50, x_47);
lean_dec(x_47);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_dec_eq(x_51, x_52);
lean_dec(x_51);
x_54 = lean_nat_add(x_7, x_50);
lean_dec(x_7);
if (x_53 == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = 1;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_46);
lean_ctor_set(x_57, 2, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_45, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_4 = x_59;
x_7 = x_54;
x_8 = x_60;
goto _start;
}
else
{
uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = 0;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_46);
lean_ctor_set(x_64, 2, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_45, x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_4 = x_66;
x_7 = x_54;
x_8 = x_67;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = l_BitVec_ofNat(x_3, x_6);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(x_1, x_2, x_3, x_4, x_8);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_array_fget(x_13, x_6);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_land(x_17, x_14);
lean_dec(x_14);
x_19 = lean_nat_dec_eq(x_18, x_6);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = 1;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
lean_inc(x_12);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_10, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg(x_1, x_2, x_3, x_24, x_12, x_13, x_17, x_25);
lean_dec(x_13);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
lean_inc(x_12);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_12);
lean_ctor_set(x_29, 2, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_10, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___rarg(x_1, x_2, x_3, x_31, x_12, x_13, x_17, x_32);
lean_dec(x_13);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
x_34 = l_Std_Sat_AIG_RefVec_empty(lean_box(0), x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Sat_AIG_RefVec_countKnown_go___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = l_Std_Sat_AIG_RefVec_countKnown_go___rarg(x_1, x_2, x_3, x_4, x_9, x_7, x_7);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_14);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(x_1, x_2, x_3, x_4, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(x_1, x_2, x_3, x_4, x_18);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___rarg(x_1, x_2, x_3, x_4, x_5);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
