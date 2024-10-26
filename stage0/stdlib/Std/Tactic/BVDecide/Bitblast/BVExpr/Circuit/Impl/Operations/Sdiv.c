// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sdiv
// Imports: Std.Sat.AIG.If Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_11 = lean_ctor_get(x_5, 5);
x_12 = lean_ctor_get(x_5, 6);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_6, x_13);
x_15 = lean_array_fget(x_8, x_14);
x_16 = lean_array_fget(x_7, x_14);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_10);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_9);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_4, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_12);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_11);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_19, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_20);
x_26 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_23, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_4, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_12, x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_16, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_17);
lean_inc(x_9);
lean_ctor_set(x_14, 0, x_9);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_19, x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_22, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_13);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_13);
lean_ctor_set(x_27, 1, x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_25, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_29, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_17);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_32, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_3);
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_3);
lean_ctor_set(x_38, 1, x_9);
lean_ctor_set(x_38, 2, x_10);
lean_ctor_set(x_38, 3, x_20);
lean_ctor_set(x_38, 4, x_26);
lean_ctor_set(x_38, 5, x_33);
lean_ctor_set(x_38, 6, x_37);
x_39 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(x_1, x_2, x_3, x_36, x_38);
lean_dec(x_38);
lean_dec(x_3);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_40, x_5);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_41);
lean_inc(x_9);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_9);
lean_ctor_set(x_45, 1, x_41);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_43, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_2);
lean_inc(x_1);
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_47, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_10);
lean_inc(x_13);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_13);
lean_ctor_set(x_52, 1, x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_50, x_52);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_2);
lean_inc(x_1);
x_56 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_54, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_13);
lean_ctor_set(x_59, 1, x_41);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_60 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_57, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_3);
x_63 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_9);
lean_ctor_set(x_63, 2, x_10);
lean_ctor_set(x_63, 3, x_44);
lean_ctor_set(x_63, 4, x_51);
lean_ctor_set(x_63, 5, x_58);
lean_ctor_set(x_63, 6, x_62);
x_64 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(x_1, x_2, x_3, x_61, x_63);
lean_dec(x_63);
lean_dec(x_3);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_65 = lean_ctor_get(x_5, 0);
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_5);
lean_inc(x_65);
lean_inc(x_2);
lean_inc(x_1);
x_67 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_4, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_inc(x_66);
lean_inc(x_2);
lean_inc(x_1);
x_70 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_68, x_66);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
lean_inc(x_66);
lean_inc(x_65);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_65);
lean_ctor_set(x_74, 1, x_66);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_75 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_71, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_72);
lean_inc(x_65);
if (lean_is_scalar(x_73)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_73;
}
lean_ctor_set(x_78, 0, x_65);
lean_ctor_set(x_78, 1, x_72);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_79 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_76, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_2);
lean_inc(x_1);
x_82 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_80, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_66);
lean_inc(x_69);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_69);
lean_ctor_set(x_85, 1, x_66);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_83, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_2);
lean_inc(x_1);
x_89 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___rarg(x_1, x_2, x_3, x_87, x_88);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_69);
lean_ctor_set(x_92, 1, x_72);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_93 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___rarg(x_1, x_2, x_3, x_90, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_3);
x_96 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_96, 0, x_3);
lean_ctor_set(x_96, 1, x_65);
lean_ctor_set(x_96, 2, x_66);
lean_ctor_set(x_96, 3, x_77);
lean_ctor_set(x_96, 4, x_84);
lean_ctor_set(x_96, 5, x_91);
lean_ctor_set(x_96, 6, x_95);
x_97 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv_signBranch___rarg(x_1, x_2, x_3, x_94, x_96);
lean_dec(x_96);
lean_dec(x_3);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_5);
lean_dec(x_3);
x_98 = l_Std_Sat_AIG_RefVec_empty(lean_box(0), x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_4);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSdiv___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sdiv(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_If(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
