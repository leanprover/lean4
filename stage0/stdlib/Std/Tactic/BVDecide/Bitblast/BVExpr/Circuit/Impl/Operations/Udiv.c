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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Sat_AIG_RefVec_empty(lean_box(0), x_1, x_2, x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_10, x_3);
x_12 = lean_array_push(x_9, x_8);
x_13 = l_Array_append___rarg(x_12, x_7);
lean_dec(x_7);
lean_ctor_set(x_5, 1, x_13);
lean_ctor_set(x_5, 0, x_11);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = l_Std_Sat_AIG_RefVec_empty(lean_box(0), x_1, x_2, x_4);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_18, x_3);
x_20 = lean_array_push(x_17, x_16);
x_21 = l_Array_append___rarg(x_20, x_15);
lean_dec(x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___rarg(x_1, x_2, x_3, x_4, x_22);
lean_dec(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_9, x_13);
x_15 = lean_nat_add(x_10, x_13);
x_16 = lean_nat_dec_lt(x_14, x_3);
if (x_16 == 0)
{
lean_inc(x_5);
x_17 = x_5;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_array_fget(x_7, x_14);
x_17 = x_99;
goto block_98;
}
block_98:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_4, x_18);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_11);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 0, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_21, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 0, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_25, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___rarg(x_1, x_2, x_3, x_28, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_22);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(x_1, x_2, x_3, x_32, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_29);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_36, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_22);
lean_ctor_set(x_42, 2, x_33);
x_43 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_40, x_42);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_14);
lean_ctor_set(x_46, 2, x_15);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_50 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_47, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_8);
lean_inc(x_22);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___rarg(x_1, x_2, x_3, x_51, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_22);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_22);
lean_ctor_set(x_57, 1, x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(x_1, x_2, x_3, x_55, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_52);
lean_inc(x_2);
lean_inc(x_1);
x_62 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_59, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_22);
lean_ctor_set(x_65, 2, x_56);
x_66 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_63, x_65);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_14);
lean_ctor_set(x_69, 2, x_15);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set(x_69, 4, x_68);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_70 = lean_ctor_get(x_19, 0);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_19);
lean_inc(x_11);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_11);
lean_ctor_set(x_72, 1, x_5);
lean_inc(x_2);
lean_inc(x_1);
x_73 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_70, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_11);
lean_ctor_set(x_77, 1, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_78 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___rarg(x_1, x_2, x_3, x_74, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_71);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___rarg(x_1, x_2, x_3, x_79, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_71);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(x_1, x_2, x_3, x_83, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_88);
x_89 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
lean_ctor_set(x_89, 2, x_80);
lean_inc(x_2);
lean_inc(x_1);
x_90 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_87, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_71);
lean_ctor_set(x_93, 2, x_84);
x_94 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_91, x_93);
lean_dec(x_3);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_14);
lean_ctor_set(x_97, 2, x_15);
lean_ctor_set(x_97, 3, x_92);
lean_ctor_set(x_97, 4, x_96);
return x_97;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg___boxed), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 4);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_19, x_17, x_6, x_7, x_8, x_9, x_20, x_21, x_22, x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_12);
lean_ctor_set(x_30, 2, x_13);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_BitVec_ofNat(x_3, x_6);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(x_1, x_2, x_3, x_4, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_9, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_13, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_21);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_21);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(x_1, x_2, x_3, x_17, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc_n(x_10, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_23, x_3, x_14, x_18, x_20, x_21, x_3, x_6, x_10, x_10);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_26, x_28);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(x_1, x_2, x_3, x_17, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc_n(x_10, 2);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_34, x_3, x_14, x_18, x_30, x_31, x_3, x_6, x_10, x_10);
lean_dec(x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_10);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_37, x_39);
lean_dec(x_3);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg), 5, 0);
return x_2;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
