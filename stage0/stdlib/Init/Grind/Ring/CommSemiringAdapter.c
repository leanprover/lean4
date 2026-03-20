// Lean compiler output
// Module: Init.Grind.Ring.CommSemiringAdapter
// Imports: public import Init.Grind.Ring.Envelope public import Init.Grind.Ring.CommSolver import Init.Data.Int.LemmasAux import Init.Omega
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
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object*, lean_object*);
uint8_t l_Lean_Grind_CommRing_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__0;
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__nc__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___redArg(lean_object* v_inst_1_, lean_object* v_ctx_2_, lean_object* v_x_3_){
_start:
{
switch(lean_obj_tag(v_x_3_))
{
case 0:
{
lean_object* v_ofNat_4_; lean_object* v_k_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_ofNat_4_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_ofNat_4_);
lean_dec_ref(v_inst_1_);
v_k_5_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_k_5_);
lean_dec_ref(v_x_3_);
v___x_6_ = lean_nat_abs(v_k_5_);
lean_dec(v_k_5_);
v___x_7_ = lean_apply_1(v_ofNat_4_, v___x_6_);
return v___x_7_;
}
case 1:
{
lean_object* v_ofNat_8_; lean_object* v_k_9_; lean_object* v___x_10_; 
v_ofNat_8_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_ofNat_8_);
lean_dec_ref(v_inst_1_);
v_k_9_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_k_9_);
lean_dec_ref(v_x_3_);
v___x_10_ = lean_apply_1(v_ofNat_8_, v_k_9_);
return v___x_10_;
}
case 3:
{
lean_object* v_i_11_; lean_object* v___x_12_; 
lean_dec_ref(v_inst_1_);
v_i_11_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_i_11_);
lean_dec_ref(v_x_3_);
v___x_12_ = l_Lean_RArray_getImpl___redArg(v_ctx_2_, v_i_11_);
lean_dec(v_i_11_);
return v___x_12_;
}
case 5:
{
lean_object* v_toAdd_13_; lean_object* v_a_14_; lean_object* v_b_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_toAdd_13_ = lean_ctor_get(v_inst_1_, 0);
lean_inc(v_toAdd_13_);
v_a_14_ = lean_ctor_get(v_x_3_, 0);
lean_inc_ref(v_a_14_);
v_b_15_ = lean_ctor_get(v_x_3_, 1);
lean_inc_ref(v_b_15_);
lean_dec_ref(v_x_3_);
lean_inc_ref(v_inst_1_);
v___x_16_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_1_, v_ctx_2_, v_a_14_);
v___x_17_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_1_, v_ctx_2_, v_b_15_);
v___x_18_ = lean_apply_2(v_toAdd_13_, v___x_16_, v___x_17_);
return v___x_18_;
}
case 7:
{
lean_object* v_toMul_19_; lean_object* v_a_20_; lean_object* v_b_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_toMul_19_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_toMul_19_);
v_a_20_ = lean_ctor_get(v_x_3_, 0);
lean_inc_ref(v_a_20_);
v_b_21_ = lean_ctor_get(v_x_3_, 1);
lean_inc_ref(v_b_21_);
lean_dec_ref(v_x_3_);
lean_inc_ref(v_inst_1_);
v___x_22_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_1_, v_ctx_2_, v_a_20_);
v___x_23_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_1_, v_ctx_2_, v_b_21_);
v___x_24_ = lean_apply_2(v_toMul_19_, v___x_22_, v___x_23_);
return v___x_24_;
}
case 8:
{
lean_object* v_npow_25_; lean_object* v_a_26_; lean_object* v_k_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_npow_25_ = lean_ctor_get(v_inst_1_, 5);
lean_inc(v_npow_25_);
v_a_26_ = lean_ctor_get(v_x_3_, 0);
lean_inc_ref(v_a_26_);
v_k_27_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_k_27_);
lean_dec_ref(v_x_3_);
v___x_28_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_1_, v_ctx_2_, v_a_26_);
v___x_29_ = lean_apply_2(v_npow_25_, v___x_28_, v_k_27_);
return v___x_29_;
}
default: 
{
lean_object* v_ofNat_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec_ref(v_x_3_);
v_ofNat_30_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_ofNat_30_);
lean_dec_ref(v_inst_1_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_apply_1(v_ofNat_30_, v___x_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___redArg___boxed(lean_object* v_inst_33_, lean_object* v_ctx_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_33_, v_ctx_34_, v_x_35_);
lean_dec_ref(v_ctx_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_ctx_39_, lean_object* v_x_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_38_, v_ctx_39_, v_x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteS___boxed(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_ctx_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Grind_CommRing_Expr_denoteS(v_00_u03b1_42_, v_inst_43_, v_ctx_44_, v_x_45_);
lean_dec_ref(v_ctx_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(lean_object* v_inst_47_, lean_object* v_ctx_48_, lean_object* v_x_49_){
_start:
{
switch(lean_obj_tag(v_x_49_))
{
case 0:
{
lean_object* v_k_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v_k_50_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_k_50_);
lean_dec_ref(v_x_49_);
v___x_51_ = lean_nat_abs(v_k_50_);
lean_dec(v_k_50_);
v___x_52_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_47_, v___x_51_);
return v___x_52_;
}
case 1:
{
lean_object* v_k_53_; lean_object* v___x_54_; 
v_k_53_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_k_53_);
lean_dec_ref(v_x_49_);
v___x_54_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_47_, v_k_53_);
return v___x_54_;
}
case 3:
{
lean_object* v_i_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_i_55_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_i_55_);
lean_dec_ref(v_x_49_);
v___x_56_ = l_Lean_RArray_getImpl___redArg(v_ctx_48_, v_i_55_);
lean_dec(v_i_55_);
v___x_57_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_47_, v___x_56_);
return v___x_57_;
}
case 5:
{
lean_object* v_a_58_; lean_object* v_b_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_a_58_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_a_58_);
v_b_59_ = lean_ctor_get(v_x_49_, 1);
lean_inc_ref(v_b_59_);
lean_dec_ref(v_x_49_);
lean_inc_ref(v_inst_47_);
v___x_60_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_a_58_);
lean_inc_ref(v_inst_47_);
v___x_61_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_b_59_);
v___x_62_ = l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_47_, v___x_60_, v___x_61_);
return v___x_62_;
}
case 7:
{
lean_object* v_a_63_; lean_object* v_b_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_a_63_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_a_63_);
v_b_64_ = lean_ctor_get(v_x_49_, 1);
lean_inc_ref(v_b_64_);
lean_dec_ref(v_x_49_);
lean_inc_ref(v_inst_47_);
v___x_65_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_a_63_);
lean_inc_ref(v_inst_47_);
v___x_66_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_b_64_);
v___x_67_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_47_, v___x_65_, v___x_66_);
return v___x_67_;
}
case 8:
{
lean_object* v_a_68_; lean_object* v_k_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_a_68_ = lean_ctor_get(v_x_49_, 0);
lean_inc_ref(v_a_68_);
v_k_69_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_k_69_);
lean_dec_ref(v_x_49_);
lean_inc_ref(v_inst_47_);
v___x_70_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_a_68_);
v___x_71_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_47_, v___x_70_, v_k_69_);
lean_dec(v_k_69_);
return v___x_71_;
}
default: 
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec_ref(v_x_49_);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_47_, v___x_72_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg___boxed(lean_object* v_inst_74_, lean_object* v_ctx_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_74_, v_ctx_75_, v_x_76_);
lean_dec_ref(v_ctx_75_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing(lean_object* v_00_u03b1_78_, lean_object* v_inst_79_, lean_object* v_ctx_80_, lean_object* v_x_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_79_, v_ctx_80_, v_x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_denoteSAsRing___boxed(lean_object* v_00_u03b1_83_, lean_object* v_inst_84_, lean_object* v_ctx_85_, lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing(v_00_u03b1_83_, v_inst_84_, v_ctx_85_, v_x_86_);
lean_dec_ref(v_ctx_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(lean_object* v_x_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_, lean_object* v_h__3_91_, lean_object* v_h__4_92_, lean_object* v_h__5_93_, lean_object* v_h__6_94_, lean_object* v_h__7_95_, lean_object* v_h__8_96_, lean_object* v_h__9_97_){
_start:
{
switch(lean_obj_tag(v_x_88_))
{
case 0:
{
lean_object* v_k_98_; lean_object* v___x_99_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
v_k_98_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_k_98_);
lean_dec_ref(v_x_88_);
v___x_99_ = lean_apply_1(v_h__1_89_, v_k_98_);
return v___x_99_;
}
case 1:
{
lean_object* v_k_100_; lean_object* v___x_101_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__1_89_);
v_k_100_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_k_100_);
lean_dec_ref(v_x_88_);
v___x_101_ = lean_apply_1(v_h__2_90_, v_k_100_);
return v___x_101_;
}
case 2:
{
lean_object* v_k_102_; lean_object* v___x_103_; 
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_k_102_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_k_102_);
lean_dec_ref(v_x_88_);
v___x_103_ = lean_apply_1(v_h__9_97_, v_k_102_);
return v___x_103_;
}
case 3:
{
lean_object* v_i_104_; lean_object* v___x_105_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_i_104_ = lean_ctor_get(v_x_88_, 0);
lean_inc(v_i_104_);
lean_dec_ref(v_x_88_);
v___x_105_ = lean_apply_1(v_h__3_91_, v_i_104_);
return v___x_105_;
}
case 4:
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_a_106_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_a_106_);
lean_dec_ref(v_x_88_);
v___x_107_ = lean_apply_1(v_h__8_96_, v_a_106_);
return v___x_107_;
}
case 5:
{
lean_object* v_a_108_; lean_object* v_b_109_; lean_object* v___x_110_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_a_108_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_a_108_);
v_b_109_ = lean_ctor_get(v_x_88_, 1);
lean_inc_ref(v_b_109_);
lean_dec_ref(v_x_88_);
v___x_110_ = lean_apply_2(v_h__4_92_, v_a_108_, v_b_109_);
return v___x_110_;
}
case 6:
{
lean_object* v_a_111_; lean_object* v_b_112_; lean_object* v___x_113_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__6_94_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_a_111_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_a_111_);
v_b_112_ = lean_ctor_get(v_x_88_, 1);
lean_inc_ref(v_b_112_);
lean_dec_ref(v_x_88_);
v___x_113_ = lean_apply_2(v_h__7_95_, v_a_111_, v_b_112_);
return v___x_113_;
}
case 7:
{
lean_object* v_a_114_; lean_object* v_b_115_; lean_object* v___x_116_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__6_94_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_a_114_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_a_114_);
v_b_115_ = lean_ctor_get(v_x_88_, 1);
lean_inc_ref(v_b_115_);
lean_dec_ref(v_x_88_);
v___x_116_ = lean_apply_2(v_h__5_93_, v_a_114_, v_b_115_);
return v___x_116_;
}
default: 
{
lean_object* v_a_117_; lean_object* v_k_118_; lean_object* v___x_119_; 
lean_dec(v_h__9_97_);
lean_dec(v_h__8_96_);
lean_dec(v_h__7_95_);
lean_dec(v_h__5_93_);
lean_dec(v_h__4_92_);
lean_dec(v_h__3_91_);
lean_dec(v_h__2_90_);
lean_dec(v_h__1_89_);
v_a_117_ = lean_ctor_get(v_x_88_, 0);
lean_inc_ref(v_a_117_);
v_k_118_ = lean_ctor_get(v_x_88_, 1);
lean_inc(v_k_118_);
lean_dec_ref(v_x_88_);
v___x_119_ = lean_apply_2(v_h__6_94_, v_a_117_, v_k_118_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter(lean_object* v_motive_120_, lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_, lean_object* v_h__3_124_, lean_object* v_h__4_125_, lean_object* v_h__5_126_, lean_object* v_h__6_127_, lean_object* v_h__7_128_, lean_object* v_h__8_129_, lean_object* v_h__9_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(v_x_121_, v_h__1_122_, v_h__2_123_, v_h__3_124_, v_h__4_125_, v_h__5_126_, v_h__6_127_, v_h__7_128_, v_h__8_129_, v_h__9_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object* v_a_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = lean_nat_to_int(v_a_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0(void){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_nat_to_int(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object* v_x_138_){
_start:
{
switch(lean_obj_tag(v_x_138_))
{
case 0:
{
lean_object* v_k_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v_k_139_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v_x_138_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_k_139_);
lean_dec(v_x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = lean_nat_abs(v_k_139_);
lean_dec(v_k_139_);
v___x_144_ = lean_nat_to_int(v___x_143_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_144_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
case 1:
{
lean_object* v_k_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_157_; 
v_k_149_ = lean_ctor_get(v_x_138_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_157_ == 0)
{
v___x_151_ = v_x_138_;
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_k_149_);
lean_dec(v_x_138_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_157_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_nat_to_int(v_k_149_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 0);
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_155_ = v___x_151_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
case 3:
{
lean_object* v_i_158_; lean_object* v___x_159_; 
v_i_158_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_i_158_);
lean_dec_ref(v_x_138_);
v___x_159_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_158_);
return v___x_159_;
}
case 5:
{
lean_object* v_a_160_; lean_object* v_b_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_a_160_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_a_160_);
v_b_161_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_b_161_);
lean_dec_ref(v_x_138_);
v___x_162_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_160_);
v___x_163_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_161_);
v___x_164_ = l_Lean_Grind_CommRing_Poly_combine(v___x_162_, v___x_163_);
return v___x_164_;
}
case 7:
{
lean_object* v_a_165_; lean_object* v_b_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_a_165_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_a_165_);
v_b_166_ = lean_ctor_get(v_x_138_, 1);
lean_inc_ref(v_b_166_);
lean_dec_ref(v_x_138_);
v___x_167_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_165_);
v___x_168_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_166_);
v___x_169_ = l_Lean_Grind_CommRing_Poly_mul(v___x_167_, v___x_168_);
return v___x_169_;
}
case 8:
{
lean_object* v_a_170_; 
v_a_170_ = lean_ctor_get(v_x_138_, 0);
lean_inc_ref(v_a_170_);
switch(lean_obj_tag(v_a_170_))
{
case 0:
{
lean_object* v_k_171_; lean_object* v_k_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_182_; 
v_k_171_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_k_171_);
lean_dec_ref(v_x_138_);
v_k_172_ = lean_ctor_get(v_a_170_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_a_170_);
if (v_isSharedCheck_182_ == 0)
{
v___x_174_ = v_a_170_;
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_k_172_);
lean_dec(v_a_170_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_182_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_176_ = lean_nat_abs(v_k_172_);
lean_dec(v_k_172_);
v___x_177_ = lean_nat_to_int(v___x_176_);
v___x_178_ = l_Int_pow(v___x_177_, v_k_171_);
lean_dec(v_k_171_);
lean_dec(v___x_177_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_178_);
v___x_180_ = v___x_174_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
case 3:
{
lean_object* v_k_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_194_; 
v_k_183_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_194_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v_x_138_, 0);
lean_dec(v_unused_195_);
v___x_185_ = v_x_138_;
v_isShared_186_ = v_isSharedCheck_194_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_k_183_);
lean_dec(v_x_138_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_194_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_i_187_; lean_object* v___x_189_; 
v_i_187_ = lean_ctor_get(v_a_170_, 0);
lean_inc(v_i_187_);
lean_dec_ref(v_a_170_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 0);
lean_ctor_set(v___x_185_, 0, v_i_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_i_187_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_k_183_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_box(0);
v___x_191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_191_);
return v___x_192_;
}
}
}
default: 
{
lean_object* v_k_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_k_196_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_k_196_);
lean_dec_ref(v_x_138_);
v___x_197_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_170_);
v___x_198_ = l_Lean_Grind_CommRing_Poly_pow(v___x_197_, v_k_196_);
lean_dec(v_k_196_);
return v___x_198_;
}
}
}
default: 
{
lean_object* v___x_199_; 
lean_dec_ref(v_x_138_);
v___x_199_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object* v_x_200_){
_start:
{
switch(lean_obj_tag(v_x_200_))
{
case 0:
{
lean_object* v_k_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_210_; 
v_k_201_ = lean_ctor_get(v_x_200_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_210_ == 0)
{
v___x_203_ = v_x_200_;
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_k_201_);
lean_dec(v_x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_210_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_205_ = lean_nat_abs(v_k_201_);
lean_dec(v_k_201_);
v___x_206_ = lean_nat_to_int(v___x_205_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 0, v___x_206_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
case 1:
{
lean_object* v_k_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_219_; 
v_k_211_ = lean_ctor_get(v_x_200_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_219_ == 0)
{
v___x_213_ = v_x_200_;
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_k_211_);
lean_dec(v_x_200_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_219_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_nat_to_int(v_k_211_);
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 0);
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
case 3:
{
lean_object* v_i_220_; lean_object* v___x_221_; 
v_i_220_ = lean_ctor_get(v_x_200_, 0);
lean_inc(v_i_220_);
lean_dec_ref(v_x_200_);
v___x_221_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_220_);
return v___x_221_;
}
case 5:
{
lean_object* v_a_222_; lean_object* v_b_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_222_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_222_);
v_b_223_ = lean_ctor_get(v_x_200_, 1);
lean_inc_ref(v_b_223_);
lean_dec_ref(v_x_200_);
v___x_224_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_222_);
v___x_225_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_223_);
v___x_226_ = l_Lean_Grind_CommRing_Poly_combine(v___x_224_, v___x_225_);
return v___x_226_;
}
case 7:
{
lean_object* v_a_227_; lean_object* v_b_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_a_227_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_227_);
v_b_228_ = lean_ctor_get(v_x_200_, 1);
lean_inc_ref(v_b_228_);
lean_dec_ref(v_x_200_);
v___x_229_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_227_);
v___x_230_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_228_);
v___x_231_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_229_, v___x_230_);
return v___x_231_;
}
case 8:
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v_x_200_, 0);
lean_inc_ref(v_a_232_);
switch(lean_obj_tag(v_a_232_))
{
case 0:
{
lean_object* v_k_233_; lean_object* v_k_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_k_233_ = lean_ctor_get(v_x_200_, 1);
lean_inc(v_k_233_);
lean_dec_ref(v_x_200_);
v_k_234_ = lean_ctor_get(v_a_232_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_a_232_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v_a_232_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_k_234_);
lean_dec(v_a_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_238_ = lean_nat_abs(v_k_234_);
lean_dec(v_k_234_);
v___x_239_ = lean_nat_to_int(v___x_238_);
v___x_240_ = l_Int_pow(v___x_239_, v_k_233_);
lean_dec(v_k_233_);
lean_dec(v___x_239_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_240_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
case 3:
{
lean_object* v_k_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_256_; 
v_k_245_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_x_200_, 0);
lean_dec(v_unused_257_);
v___x_247_ = v_x_200_;
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_k_245_);
lean_dec(v_x_200_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v_i_249_; lean_object* v___x_251_; 
v_i_249_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_i_249_);
lean_dec_ref(v_a_232_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 0);
lean_ctor_set(v___x_247_, 0, v_i_249_);
v___x_251_ = v___x_247_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_i_249_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_k_245_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_252_ = lean_box(0);
v___x_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_253_);
return v___x_254_;
}
}
}
default: 
{
lean_object* v_k_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_k_258_ = lean_ctor_get(v_x_200_, 1);
lean_inc(v_k_258_);
lean_dec_ref(v_x_200_);
v___x_259_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_232_);
v___x_260_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_259_, v_k_258_);
lean_dec(v_k_258_);
return v___x_260_;
}
}
}
default: 
{
lean_object* v___x_261_; 
lean_dec_ref(v_x_200_);
v___x_261_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_261_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_262_, lean_object* v_k_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_266_ = lean_int_dec_lt(v_k_263_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v_ofNat_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_ofNat_267_ = lean_ctor_get(v_inst_262_, 3);
lean_inc(v_ofNat_267_);
lean_dec_ref(v_inst_262_);
v___x_268_ = lean_nat_abs(v_k_263_);
v___x_269_ = lean_apply_1(v_ofNat_267_, v___x_268_);
return v___x_269_;
}
else
{
lean_object* v_ofNat_270_; lean_object* v___x_271_; 
v_ofNat_270_ = lean_ctor_get(v_inst_262_, 3);
lean_inc(v_ofNat_270_);
lean_dec_ref(v_inst_262_);
v___x_271_ = lean_apply_1(v_ofNat_270_, v___x_264_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_272_, v_k_273_);
lean_dec(v_k_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_275_, lean_object* v_inst_276_, lean_object* v_k_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_276_, v_k_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_k_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_279_, v_inst_280_, v_k_281_);
lean_dec(v_k_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_283_, lean_object* v_ctx_284_, lean_object* v_p_285_){
_start:
{
if (lean_obj_tag(v_p_285_) == 0)
{
lean_object* v_k_286_; lean_object* v___x_287_; 
v_k_286_ = lean_ctor_get(v_p_285_, 0);
lean_inc(v_k_286_);
lean_dec_ref(v_p_285_);
v___x_287_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_283_, v_k_286_);
lean_dec(v_k_286_);
return v___x_287_;
}
else
{
lean_object* v_toAdd_288_; lean_object* v_toMul_289_; lean_object* v_k_290_; lean_object* v_v_291_; lean_object* v_p_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_toAdd_288_ = lean_ctor_get(v_inst_283_, 0);
lean_inc(v_toAdd_288_);
v_toMul_289_ = lean_ctor_get(v_inst_283_, 1);
v_k_290_ = lean_ctor_get(v_p_285_, 0);
lean_inc(v_k_290_);
v_v_291_ = lean_ctor_get(v_p_285_, 1);
lean_inc(v_v_291_);
v_p_292_ = lean_ctor_get(v_p_285_, 2);
lean_inc_ref(v_p_292_);
lean_dec_ref(v_p_285_);
lean_inc_ref(v_inst_283_);
v___x_293_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_283_, v_k_290_);
lean_dec(v_k_290_);
lean_inc_ref(v_inst_283_);
v___x_294_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_283_, v_ctx_284_, v_v_291_);
lean_inc(v_toMul_289_);
v___x_295_ = lean_apply_2(v_toMul_289_, v___x_293_, v___x_294_);
v___x_296_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_283_, v_ctx_284_, v_p_292_);
v___x_297_ = lean_apply_2(v_toAdd_288_, v___x_295_, v___x_296_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_298_, lean_object* v_ctx_299_, lean_object* v_p_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_298_, v_ctx_299_, v_p_300_);
lean_dec_ref(v_ctx_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_302_, lean_object* v_inst_303_, lean_object* v_ctx_304_, lean_object* v_p_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_303_, v_ctx_304_, v_p_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_ctx_309_, lean_object* v_p_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_307_, v_inst_308_, v_ctx_309_, v_p_310_);
lean_dec_ref(v_ctx_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object* v_p_312_, lean_object* v_h__1_313_, lean_object* v_h__2_314_){
_start:
{
if (lean_obj_tag(v_p_312_) == 0)
{
lean_object* v_k_315_; lean_object* v___x_316_; 
lean_dec(v_h__2_314_);
v_k_315_ = lean_ctor_get(v_p_312_, 0);
lean_inc(v_k_315_);
lean_dec_ref(v_p_312_);
v___x_316_ = lean_apply_1(v_h__1_313_, v_k_315_);
return v___x_316_;
}
else
{
lean_object* v_k_317_; lean_object* v_v_318_; lean_object* v_p_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_313_);
v_k_317_ = lean_ctor_get(v_p_312_, 0);
lean_inc(v_k_317_);
v_v_318_ = lean_ctor_get(v_p_312_, 1);
lean_inc(v_v_318_);
v_p_319_ = lean_ctor_get(v_p_312_, 2);
lean_inc_ref(v_p_319_);
lean_dec_ref(v_p_312_);
v___x_320_ = lean_apply_3(v_h__2_314_, v_k_317_, v_v_318_, v_p_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object* v_motive_321_, lean_object* v_p_322_, lean_object* v_h__1_323_, lean_object* v_h__2_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(v_p_322_, v_h__1_323_, v_h__2_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_326_, lean_object* v_h__1_327_, lean_object* v_h__2_328_, lean_object* v_h__3_329_, lean_object* v_h__4_330_, lean_object* v_h__5_331_, lean_object* v_h__6_332_, lean_object* v_h__7_333_, lean_object* v_h__8_334_, lean_object* v_h__9_335_){
_start:
{
switch(lean_obj_tag(v_x_326_))
{
case 0:
{
lean_object* v_k_336_; lean_object* v___x_337_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
v_k_336_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_k_336_);
lean_dec_ref(v_x_326_);
v___x_337_ = lean_apply_1(v_h__1_327_, v_k_336_);
return v___x_337_;
}
case 1:
{
lean_object* v_k_338_; lean_object* v___x_339_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_k_338_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_k_338_);
lean_dec_ref(v_x_326_);
v___x_339_ = lean_apply_1(v_h__6_332_, v_k_338_);
return v___x_339_;
}
case 2:
{
lean_object* v_k_340_; lean_object* v___x_341_; 
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_k_340_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_k_340_);
lean_dec_ref(v_x_326_);
v___x_341_ = lean_apply_1(v_h__9_335_, v_k_340_);
return v___x_341_;
}
case 3:
{
lean_object* v_i_342_; lean_object* v___x_343_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__1_327_);
v_i_342_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_i_342_);
lean_dec_ref(v_x_326_);
v___x_343_ = lean_apply_1(v_h__2_328_, v_i_342_);
return v___x_343_;
}
case 4:
{
lean_object* v_a_344_; lean_object* v___x_345_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_a_344_ = lean_ctor_get(v_x_326_, 0);
lean_inc_ref(v_a_344_);
lean_dec_ref(v_x_326_);
v___x_345_ = lean_apply_1(v_h__8_334_, v_a_344_);
return v___x_345_;
}
case 5:
{
lean_object* v_a_346_; lean_object* v_b_347_; lean_object* v___x_348_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_a_346_ = lean_ctor_get(v_x_326_, 0);
lean_inc_ref(v_a_346_);
v_b_347_ = lean_ctor_get(v_x_326_, 1);
lean_inc_ref(v_b_347_);
lean_dec_ref(v_x_326_);
v___x_348_ = lean_apply_2(v_h__3_329_, v_a_346_, v_b_347_);
return v___x_348_;
}
case 6:
{
lean_object* v_a_349_; lean_object* v_b_350_; lean_object* v___x_351_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_a_349_ = lean_ctor_get(v_x_326_, 0);
lean_inc_ref(v_a_349_);
v_b_350_ = lean_ctor_get(v_x_326_, 1);
lean_inc_ref(v_b_350_);
lean_dec_ref(v_x_326_);
v___x_351_ = lean_apply_2(v_h__7_333_, v_a_349_, v_b_350_);
return v___x_351_;
}
case 7:
{
lean_object* v_a_352_; lean_object* v_b_353_; lean_object* v___x_354_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__5_331_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_a_352_ = lean_ctor_get(v_x_326_, 0);
lean_inc_ref(v_a_352_);
v_b_353_ = lean_ctor_get(v_x_326_, 1);
lean_inc_ref(v_b_353_);
lean_dec_ref(v_x_326_);
v___x_354_ = lean_apply_2(v_h__4_330_, v_a_352_, v_b_353_);
return v___x_354_;
}
default: 
{
lean_object* v_a_355_; lean_object* v_k_356_; lean_object* v___x_357_; 
lean_dec(v_h__9_335_);
lean_dec(v_h__8_334_);
lean_dec(v_h__7_333_);
lean_dec(v_h__6_332_);
lean_dec(v_h__4_330_);
lean_dec(v_h__3_329_);
lean_dec(v_h__2_328_);
lean_dec(v_h__1_327_);
v_a_355_ = lean_ctor_get(v_x_326_, 0);
lean_inc_ref(v_a_355_);
v_k_356_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_k_356_);
lean_dec_ref(v_x_326_);
v___x_357_ = lean_apply_2(v_h__5_331_, v_a_355_, v_k_356_);
return v___x_357_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_358_, lean_object* v_x_359_, lean_object* v_h__1_360_, lean_object* v_h__2_361_, lean_object* v_h__3_362_, lean_object* v_h__4_363_, lean_object* v_h__5_364_, lean_object* v_h__6_365_, lean_object* v_h__7_366_, lean_object* v_h__8_367_, lean_object* v_h__9_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(v_x_359_, v_h__1_360_, v_h__2_361_, v_h__3_362_, v_h__4_363_, v_h__5_364_, v_h__6_365_, v_h__7_366_, v_h__8_367_, v_h__9_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_370_, lean_object* v_h__1_371_, lean_object* v_h__2_372_, lean_object* v_h__3_373_){
_start:
{
switch(lean_obj_tag(v_a_370_))
{
case 0:
{
lean_object* v_k_374_; lean_object* v___x_375_; 
lean_dec(v_h__3_373_);
lean_dec(v_h__2_372_);
v_k_374_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_k_374_);
lean_dec_ref(v_a_370_);
v___x_375_ = lean_apply_1(v_h__1_371_, v_k_374_);
return v___x_375_;
}
case 3:
{
lean_object* v_i_376_; lean_object* v___x_377_; 
lean_dec(v_h__3_373_);
lean_dec(v_h__1_371_);
v_i_376_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_i_376_);
lean_dec_ref(v_a_370_);
v___x_377_ = lean_apply_1(v_h__2_372_, v_i_376_);
return v___x_377_;
}
default: 
{
lean_object* v___x_378_; 
lean_dec(v_h__2_372_);
lean_dec(v_h__1_371_);
v___x_378_ = lean_apply_3(v_h__3_373_, v_a_370_, lean_box(0), lean_box(0));
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_379_, lean_object* v_a_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_, lean_object* v_h__3_383_){
_start:
{
switch(lean_obj_tag(v_a_380_))
{
case 0:
{
lean_object* v_k_384_; lean_object* v___x_385_; 
lean_dec(v_h__3_383_);
lean_dec(v_h__2_382_);
v_k_384_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_k_384_);
lean_dec_ref(v_a_380_);
v___x_385_ = lean_apply_1(v_h__1_381_, v_k_384_);
return v___x_385_;
}
case 3:
{
lean_object* v_i_386_; lean_object* v___x_387_; 
lean_dec(v_h__3_383_);
lean_dec(v_h__1_381_);
v_i_386_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_i_386_);
lean_dec_ref(v_a_380_);
v___x_387_ = lean_apply_1(v_h__2_382_, v_i_386_);
return v___x_387_;
}
default: 
{
lean_object* v___x_388_; 
lean_dec(v_h__2_382_);
lean_dec(v_h__1_381_);
v___x_388_ = lean_apply_3(v_h__3_383_, v_a_380_, lean_box(0), lean_box(0));
return v___x_388_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__cert(lean_object* v_lhs_389_, lean_object* v_rhs_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_391_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_389_);
v___x_392_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_390_);
v___x_393_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_391_, v___x_392_);
lean_dec_ref(v___x_392_);
lean_dec_ref(v___x_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__cert___boxed(lean_object* v_lhs_394_, lean_object* v_rhs_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_394_, v_rhs_395_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__nc__cert(lean_object* v_lhs_398_, lean_object* v_rhs_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_398_);
v___x_401_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_399_);
v___x_402_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_400_, v___x_401_);
lean_dec_ref(v___x_401_);
lean_dec_ref(v___x_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(lean_object* v_lhs_403_, lean_object* v_rhs_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_403_, v_rhs_404_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_CommSolver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
}
#ifdef __cplusplus
}
#endif
