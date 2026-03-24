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
switch(lean_obj_tag(v_x_121_))
{
case 0:
{
lean_object* v_k_131_; lean_object* v___x_132_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
v_k_131_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_k_131_);
lean_dec_ref(v_x_121_);
v___x_132_ = lean_apply_1(v_h__1_122_, v_k_131_);
return v___x_132_;
}
case 1:
{
lean_object* v_k_133_; lean_object* v___x_134_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__1_122_);
v_k_133_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_k_133_);
lean_dec_ref(v_x_121_);
v___x_134_ = lean_apply_1(v_h__2_123_, v_k_133_);
return v___x_134_;
}
case 2:
{
lean_object* v_k_135_; lean_object* v___x_136_; 
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_k_135_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_k_135_);
lean_dec_ref(v_x_121_);
v___x_136_ = lean_apply_1(v_h__9_130_, v_k_135_);
return v___x_136_;
}
case 3:
{
lean_object* v_i_137_; lean_object* v___x_138_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_i_137_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_i_137_);
lean_dec_ref(v_x_121_);
v___x_138_ = lean_apply_1(v_h__3_124_, v_i_137_);
return v___x_138_;
}
case 4:
{
lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_a_139_ = lean_ctor_get(v_x_121_, 0);
lean_inc_ref(v_a_139_);
lean_dec_ref(v_x_121_);
v___x_140_ = lean_apply_1(v_h__8_129_, v_a_139_);
return v___x_140_;
}
case 5:
{
lean_object* v_a_141_; lean_object* v_b_142_; lean_object* v___x_143_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_a_141_ = lean_ctor_get(v_x_121_, 0);
lean_inc_ref(v_a_141_);
v_b_142_ = lean_ctor_get(v_x_121_, 1);
lean_inc_ref(v_b_142_);
lean_dec_ref(v_x_121_);
v___x_143_ = lean_apply_2(v_h__4_125_, v_a_141_, v_b_142_);
return v___x_143_;
}
case 6:
{
lean_object* v_a_144_; lean_object* v_b_145_; lean_object* v___x_146_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__6_127_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_a_144_ = lean_ctor_get(v_x_121_, 0);
lean_inc_ref(v_a_144_);
v_b_145_ = lean_ctor_get(v_x_121_, 1);
lean_inc_ref(v_b_145_);
lean_dec_ref(v_x_121_);
v___x_146_ = lean_apply_2(v_h__7_128_, v_a_144_, v_b_145_);
return v___x_146_;
}
case 7:
{
lean_object* v_a_147_; lean_object* v_b_148_; lean_object* v___x_149_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__6_127_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_a_147_ = lean_ctor_get(v_x_121_, 0);
lean_inc_ref(v_a_147_);
v_b_148_ = lean_ctor_get(v_x_121_, 1);
lean_inc_ref(v_b_148_);
lean_dec_ref(v_x_121_);
v___x_149_ = lean_apply_2(v_h__5_126_, v_a_147_, v_b_148_);
return v___x_149_;
}
default: 
{
lean_object* v_a_150_; lean_object* v_k_151_; lean_object* v___x_152_; 
lean_dec(v_h__9_130_);
lean_dec(v_h__8_129_);
lean_dec(v_h__7_128_);
lean_dec(v_h__5_126_);
lean_dec(v_h__4_125_);
lean_dec(v_h__3_124_);
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v_a_150_ = lean_ctor_get(v_x_121_, 0);
lean_inc_ref(v_a_150_);
v_k_151_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_k_151_);
lean_dec_ref(v_x_121_);
v___x_152_ = lean_apply_2(v_h__6_127_, v_a_150_, v_k_151_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_nat_to_int(v_a_153_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = lean_nat_to_int(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object* v_x_159_){
_start:
{
switch(lean_obj_tag(v_x_159_))
{
case 0:
{
lean_object* v_k_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_169_; 
v_k_160_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_169_ == 0)
{
v___x_162_ = v_x_159_;
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_k_160_);
lean_dec(v_x_159_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_169_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_164_ = lean_nat_abs(v_k_160_);
lean_dec(v_k_160_);
v___x_165_ = lean_nat_to_int(v___x_164_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_165_);
v___x_167_ = v___x_162_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
case 1:
{
lean_object* v_k_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
v_k_170_ = lean_ctor_get(v_x_159_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v_x_159_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_k_170_);
lean_dec(v_x_159_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_nat_to_int(v_k_170_);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 0);
lean_ctor_set(v___x_172_, 0, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
case 3:
{
lean_object* v_i_179_; lean_object* v___x_180_; 
v_i_179_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_i_179_);
lean_dec_ref(v_x_159_);
v___x_180_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_179_);
return v___x_180_;
}
case 5:
{
lean_object* v_a_181_; lean_object* v_b_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_181_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_a_181_);
v_b_182_ = lean_ctor_get(v_x_159_, 1);
lean_inc_ref(v_b_182_);
lean_dec_ref(v_x_159_);
v___x_183_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_181_);
v___x_184_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_182_);
v___x_185_ = l_Lean_Grind_CommRing_Poly_combine(v___x_183_, v___x_184_);
return v___x_185_;
}
case 7:
{
lean_object* v_a_186_; lean_object* v_b_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_a_186_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_a_186_);
v_b_187_ = lean_ctor_get(v_x_159_, 1);
lean_inc_ref(v_b_187_);
lean_dec_ref(v_x_159_);
v___x_188_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_186_);
v___x_189_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_187_);
v___x_190_ = l_Lean_Grind_CommRing_Poly_mul(v___x_188_, v___x_189_);
return v___x_190_;
}
case 8:
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v_x_159_, 0);
lean_inc_ref(v_a_191_);
switch(lean_obj_tag(v_a_191_))
{
case 0:
{
lean_object* v_k_192_; lean_object* v_k_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_203_; 
v_k_192_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_k_192_);
lean_dec_ref(v_x_159_);
v_k_193_ = lean_ctor_get(v_a_191_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_203_ == 0)
{
v___x_195_ = v_a_191_;
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_k_193_);
lean_dec(v_a_191_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_203_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_197_ = lean_nat_abs(v_k_193_);
lean_dec(v_k_193_);
v___x_198_ = lean_nat_to_int(v___x_197_);
v___x_199_ = l_Int_pow(v___x_198_, v_k_192_);
lean_dec(v_k_192_);
lean_dec(v___x_198_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_199_);
v___x_201_ = v___x_195_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
case 3:
{
lean_object* v_k_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_215_; 
v_k_204_ = lean_ctor_get(v_x_159_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_x_159_);
if (v_isSharedCheck_215_ == 0)
{
lean_object* v_unused_216_; 
v_unused_216_ = lean_ctor_get(v_x_159_, 0);
lean_dec(v_unused_216_);
v___x_206_ = v_x_159_;
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_k_204_);
lean_dec(v_x_159_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_i_208_; lean_object* v___x_210_; 
v_i_208_ = lean_ctor_get(v_a_191_, 0);
lean_inc(v_i_208_);
lean_dec_ref(v_a_191_);
if (v_isShared_207_ == 0)
{
lean_ctor_set_tag(v___x_206_, 0);
lean_ctor_set(v___x_206_, 0, v_i_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_i_208_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_k_204_);
v___x_210_ = v_reuseFailAlloc_214_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_212_);
return v___x_213_;
}
}
}
default: 
{
lean_object* v_k_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_k_217_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_k_217_);
lean_dec_ref(v_x_159_);
v___x_218_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_191_);
v___x_219_ = l_Lean_Grind_CommRing_Poly_pow(v___x_218_, v_k_217_);
lean_dec(v_k_217_);
return v___x_219_;
}
}
}
default: 
{
lean_object* v___x_220_; 
lean_dec_ref(v_x_159_);
v___x_220_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object* v_x_221_){
_start:
{
switch(lean_obj_tag(v_x_221_))
{
case 0:
{
lean_object* v_k_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_231_; 
v_k_222_ = lean_ctor_get(v_x_221_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_231_ == 0)
{
v___x_224_ = v_x_221_;
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_k_222_);
lean_dec(v_x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = lean_nat_abs(v_k_222_);
lean_dec(v_k_222_);
v___x_227_ = lean_nat_to_int(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_227_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
case 1:
{
lean_object* v_k_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_240_; 
v_k_232_ = lean_ctor_get(v_x_221_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_240_ == 0)
{
v___x_234_ = v_x_221_;
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_k_232_);
lean_dec(v_x_221_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_240_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_236_ = lean_nat_to_int(v_k_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set_tag(v___x_234_, 0);
lean_ctor_set(v___x_234_, 0, v___x_236_);
v___x_238_ = v___x_234_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
case 3:
{
lean_object* v_i_241_; lean_object* v___x_242_; 
v_i_241_ = lean_ctor_get(v_x_221_, 0);
lean_inc(v_i_241_);
lean_dec_ref(v_x_221_);
v___x_242_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_241_);
return v___x_242_;
}
case 5:
{
lean_object* v_a_243_; lean_object* v_b_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_243_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_a_243_);
v_b_244_ = lean_ctor_get(v_x_221_, 1);
lean_inc_ref(v_b_244_);
lean_dec_ref(v_x_221_);
v___x_245_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_243_);
v___x_246_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_244_);
v___x_247_ = l_Lean_Grind_CommRing_Poly_combine(v___x_245_, v___x_246_);
return v___x_247_;
}
case 7:
{
lean_object* v_a_248_; lean_object* v_b_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_a_248_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_a_248_);
v_b_249_ = lean_ctor_get(v_x_221_, 1);
lean_inc_ref(v_b_249_);
lean_dec_ref(v_x_221_);
v___x_250_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_248_);
v___x_251_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_249_);
v___x_252_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_250_, v___x_251_);
return v___x_252_;
}
case 8:
{
lean_object* v_a_253_; 
v_a_253_ = lean_ctor_get(v_x_221_, 0);
lean_inc_ref(v_a_253_);
switch(lean_obj_tag(v_a_253_))
{
case 0:
{
lean_object* v_k_254_; lean_object* v_k_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_265_; 
v_k_254_ = lean_ctor_get(v_x_221_, 1);
lean_inc(v_k_254_);
lean_dec_ref(v_x_221_);
v_k_255_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_265_ == 0)
{
v___x_257_ = v_a_253_;
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_k_255_);
lean_dec(v_a_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_265_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_259_ = lean_nat_abs(v_k_255_);
lean_dec(v_k_255_);
v___x_260_ = lean_nat_to_int(v___x_259_);
v___x_261_ = l_Int_pow(v___x_260_, v_k_254_);
lean_dec(v_k_254_);
lean_dec(v___x_260_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_261_);
v___x_263_ = v___x_257_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
case 3:
{
lean_object* v_k_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_277_; 
v_k_266_ = lean_ctor_get(v_x_221_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_221_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_x_221_, 0);
lean_dec(v_unused_278_);
v___x_268_ = v_x_221_;
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_k_266_);
lean_dec(v_x_221_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_277_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_i_270_; lean_object* v___x_272_; 
v_i_270_ = lean_ctor_get(v_a_253_, 0);
lean_inc(v_i_270_);
lean_dec_ref(v_a_253_);
if (v_isShared_269_ == 0)
{
lean_ctor_set_tag(v___x_268_, 0);
lean_ctor_set(v___x_268_, 0, v_i_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_i_270_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_k_266_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_274_);
return v___x_275_;
}
}
}
default: 
{
lean_object* v_k_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v_k_279_ = lean_ctor_get(v_x_221_, 1);
lean_inc(v_k_279_);
lean_dec_ref(v_x_221_);
v___x_280_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_253_);
v___x_281_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_280_, v_k_279_);
lean_dec(v_k_279_);
return v___x_281_;
}
}
}
default: 
{
lean_object* v___x_282_; 
lean_dec_ref(v_x_221_);
v___x_282_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_283_, lean_object* v_k_284_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_287_ = lean_int_dec_lt(v_k_284_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v_ofNat_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_ofNat_288_ = lean_ctor_get(v_inst_283_, 3);
lean_inc(v_ofNat_288_);
lean_dec_ref(v_inst_283_);
v___x_289_ = lean_nat_abs(v_k_284_);
v___x_290_ = lean_apply_1(v_ofNat_288_, v___x_289_);
return v___x_290_;
}
else
{
lean_object* v_ofNat_291_; lean_object* v___x_292_; 
v_ofNat_291_ = lean_ctor_get(v_inst_283_, 3);
lean_inc(v_ofNat_291_);
lean_dec_ref(v_inst_283_);
v___x_292_ = lean_apply_1(v_ofNat_291_, v___x_285_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_293_, lean_object* v_k_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_293_, v_k_294_);
lean_dec(v_k_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_296_, lean_object* v_inst_297_, lean_object* v_k_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_297_, v_k_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_k_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_300_, v_inst_301_, v_k_302_);
lean_dec(v_k_302_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_304_, lean_object* v_ctx_305_, lean_object* v_p_306_){
_start:
{
if (lean_obj_tag(v_p_306_) == 0)
{
lean_object* v_k_307_; lean_object* v___x_308_; 
v_k_307_ = lean_ctor_get(v_p_306_, 0);
lean_inc(v_k_307_);
lean_dec_ref(v_p_306_);
v___x_308_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_304_, v_k_307_);
lean_dec(v_k_307_);
return v___x_308_;
}
else
{
lean_object* v_toAdd_309_; lean_object* v_toMul_310_; lean_object* v_k_311_; lean_object* v_v_312_; lean_object* v_p_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_toAdd_309_ = lean_ctor_get(v_inst_304_, 0);
lean_inc(v_toAdd_309_);
v_toMul_310_ = lean_ctor_get(v_inst_304_, 1);
v_k_311_ = lean_ctor_get(v_p_306_, 0);
lean_inc(v_k_311_);
v_v_312_ = lean_ctor_get(v_p_306_, 1);
lean_inc(v_v_312_);
v_p_313_ = lean_ctor_get(v_p_306_, 2);
lean_inc_ref(v_p_313_);
lean_dec_ref(v_p_306_);
lean_inc_ref(v_inst_304_);
v___x_314_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_304_, v_k_311_);
lean_dec(v_k_311_);
lean_inc_ref(v_inst_304_);
v___x_315_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_304_, v_ctx_305_, v_v_312_);
lean_inc(v_toMul_310_);
v___x_316_ = lean_apply_2(v_toMul_310_, v___x_314_, v___x_315_);
v___x_317_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_304_, v_ctx_305_, v_p_313_);
v___x_318_ = lean_apply_2(v_toAdd_309_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_319_, lean_object* v_ctx_320_, lean_object* v_p_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_319_, v_ctx_320_, v_p_321_);
lean_dec_ref(v_ctx_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_ctx_325_, lean_object* v_p_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_324_, v_ctx_325_, v_p_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_328_, lean_object* v_inst_329_, lean_object* v_ctx_330_, lean_object* v_p_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_328_, v_inst_329_, v_ctx_330_, v_p_331_);
lean_dec_ref(v_ctx_330_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object* v_p_333_, lean_object* v_h__1_334_, lean_object* v_h__2_335_){
_start:
{
if (lean_obj_tag(v_p_333_) == 0)
{
lean_object* v_k_336_; lean_object* v___x_337_; 
lean_dec(v_h__2_335_);
v_k_336_ = lean_ctor_get(v_p_333_, 0);
lean_inc(v_k_336_);
lean_dec_ref(v_p_333_);
v___x_337_ = lean_apply_1(v_h__1_334_, v_k_336_);
return v___x_337_;
}
else
{
lean_object* v_k_338_; lean_object* v_v_339_; lean_object* v_p_340_; lean_object* v___x_341_; 
lean_dec(v_h__1_334_);
v_k_338_ = lean_ctor_get(v_p_333_, 0);
lean_inc(v_k_338_);
v_v_339_ = lean_ctor_get(v_p_333_, 1);
lean_inc(v_v_339_);
v_p_340_ = lean_ctor_get(v_p_333_, 2);
lean_inc_ref(v_p_340_);
lean_dec_ref(v_p_333_);
v___x_341_ = lean_apply_3(v_h__2_335_, v_k_338_, v_v_339_, v_p_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object* v_motive_342_, lean_object* v_p_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
if (lean_obj_tag(v_p_343_) == 0)
{
lean_object* v_k_346_; lean_object* v___x_347_; 
lean_dec(v_h__2_345_);
v_k_346_ = lean_ctor_get(v_p_343_, 0);
lean_inc(v_k_346_);
lean_dec_ref(v_p_343_);
v___x_347_ = lean_apply_1(v_h__1_344_, v_k_346_);
return v___x_347_;
}
else
{
lean_object* v_k_348_; lean_object* v_v_349_; lean_object* v_p_350_; lean_object* v___x_351_; 
lean_dec(v_h__1_344_);
v_k_348_ = lean_ctor_get(v_p_343_, 0);
lean_inc(v_k_348_);
v_v_349_ = lean_ctor_get(v_p_343_, 1);
lean_inc(v_v_349_);
v_p_350_ = lean_ctor_get(v_p_343_, 2);
lean_inc_ref(v_p_350_);
lean_dec_ref(v_p_343_);
v___x_351_ = lean_apply_3(v_h__2_345_, v_k_348_, v_v_349_, v_p_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_352_, lean_object* v_h__1_353_, lean_object* v_h__2_354_, lean_object* v_h__3_355_, lean_object* v_h__4_356_, lean_object* v_h__5_357_, lean_object* v_h__6_358_, lean_object* v_h__7_359_, lean_object* v_h__8_360_, lean_object* v_h__9_361_){
_start:
{
switch(lean_obj_tag(v_x_352_))
{
case 0:
{
lean_object* v_k_362_; lean_object* v___x_363_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
v_k_362_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_k_362_);
lean_dec_ref(v_x_352_);
v___x_363_ = lean_apply_1(v_h__1_353_, v_k_362_);
return v___x_363_;
}
case 1:
{
lean_object* v_k_364_; lean_object* v___x_365_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_k_364_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_k_364_);
lean_dec_ref(v_x_352_);
v___x_365_ = lean_apply_1(v_h__6_358_, v_k_364_);
return v___x_365_;
}
case 2:
{
lean_object* v_k_366_; lean_object* v___x_367_; 
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_k_366_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_k_366_);
lean_dec_ref(v_x_352_);
v___x_367_ = lean_apply_1(v_h__9_361_, v_k_366_);
return v___x_367_;
}
case 3:
{
lean_object* v_i_368_; lean_object* v___x_369_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__1_353_);
v_i_368_ = lean_ctor_get(v_x_352_, 0);
lean_inc(v_i_368_);
lean_dec_ref(v_x_352_);
v___x_369_ = lean_apply_1(v_h__2_354_, v_i_368_);
return v___x_369_;
}
case 4:
{
lean_object* v_a_370_; lean_object* v___x_371_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_a_370_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_a_370_);
lean_dec_ref(v_x_352_);
v___x_371_ = lean_apply_1(v_h__8_360_, v_a_370_);
return v___x_371_;
}
case 5:
{
lean_object* v_a_372_; lean_object* v_b_373_; lean_object* v___x_374_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_a_372_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_a_372_);
v_b_373_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_b_373_);
lean_dec_ref(v_x_352_);
v___x_374_ = lean_apply_2(v_h__3_355_, v_a_372_, v_b_373_);
return v___x_374_;
}
case 6:
{
lean_object* v_a_375_; lean_object* v_b_376_; lean_object* v___x_377_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_a_375_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_a_375_);
v_b_376_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_b_376_);
lean_dec_ref(v_x_352_);
v___x_377_ = lean_apply_2(v_h__7_359_, v_a_375_, v_b_376_);
return v___x_377_;
}
case 7:
{
lean_object* v_a_378_; lean_object* v_b_379_; lean_object* v___x_380_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__5_357_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_a_378_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_a_378_);
v_b_379_ = lean_ctor_get(v_x_352_, 1);
lean_inc_ref(v_b_379_);
lean_dec_ref(v_x_352_);
v___x_380_ = lean_apply_2(v_h__4_356_, v_a_378_, v_b_379_);
return v___x_380_;
}
default: 
{
lean_object* v_a_381_; lean_object* v_k_382_; lean_object* v___x_383_; 
lean_dec(v_h__9_361_);
lean_dec(v_h__8_360_);
lean_dec(v_h__7_359_);
lean_dec(v_h__6_358_);
lean_dec(v_h__4_356_);
lean_dec(v_h__3_355_);
lean_dec(v_h__2_354_);
lean_dec(v_h__1_353_);
v_a_381_ = lean_ctor_get(v_x_352_, 0);
lean_inc_ref(v_a_381_);
v_k_382_ = lean_ctor_get(v_x_352_, 1);
lean_inc(v_k_382_);
lean_dec_ref(v_x_352_);
v___x_383_ = lean_apply_2(v_h__5_357_, v_a_381_, v_k_382_);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_384_, lean_object* v_x_385_, lean_object* v_h__1_386_, lean_object* v_h__2_387_, lean_object* v_h__3_388_, lean_object* v_h__4_389_, lean_object* v_h__5_390_, lean_object* v_h__6_391_, lean_object* v_h__7_392_, lean_object* v_h__8_393_, lean_object* v_h__9_394_){
_start:
{
switch(lean_obj_tag(v_x_385_))
{
case 0:
{
lean_object* v_k_395_; lean_object* v___x_396_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
v_k_395_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_k_395_);
lean_dec_ref(v_x_385_);
v___x_396_ = lean_apply_1(v_h__1_386_, v_k_395_);
return v___x_396_;
}
case 1:
{
lean_object* v_k_397_; lean_object* v___x_398_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_k_397_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_k_397_);
lean_dec_ref(v_x_385_);
v___x_398_ = lean_apply_1(v_h__6_391_, v_k_397_);
return v___x_398_;
}
case 2:
{
lean_object* v_k_399_; lean_object* v___x_400_; 
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_k_399_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_k_399_);
lean_dec_ref(v_x_385_);
v___x_400_ = lean_apply_1(v_h__9_394_, v_k_399_);
return v___x_400_;
}
case 3:
{
lean_object* v_i_401_; lean_object* v___x_402_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__1_386_);
v_i_401_ = lean_ctor_get(v_x_385_, 0);
lean_inc(v_i_401_);
lean_dec_ref(v_x_385_);
v___x_402_ = lean_apply_1(v_h__2_387_, v_i_401_);
return v___x_402_;
}
case 4:
{
lean_object* v_a_403_; lean_object* v___x_404_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_a_403_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_a_403_);
lean_dec_ref(v_x_385_);
v___x_404_ = lean_apply_1(v_h__8_393_, v_a_403_);
return v___x_404_;
}
case 5:
{
lean_object* v_a_405_; lean_object* v_b_406_; lean_object* v___x_407_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_a_405_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_a_405_);
v_b_406_ = lean_ctor_get(v_x_385_, 1);
lean_inc_ref(v_b_406_);
lean_dec_ref(v_x_385_);
v___x_407_ = lean_apply_2(v_h__3_388_, v_a_405_, v_b_406_);
return v___x_407_;
}
case 6:
{
lean_object* v_a_408_; lean_object* v_b_409_; lean_object* v___x_410_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_a_408_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_a_408_);
v_b_409_ = lean_ctor_get(v_x_385_, 1);
lean_inc_ref(v_b_409_);
lean_dec_ref(v_x_385_);
v___x_410_ = lean_apply_2(v_h__7_392_, v_a_408_, v_b_409_);
return v___x_410_;
}
case 7:
{
lean_object* v_a_411_; lean_object* v_b_412_; lean_object* v___x_413_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__5_390_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_a_411_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_a_411_);
v_b_412_ = lean_ctor_get(v_x_385_, 1);
lean_inc_ref(v_b_412_);
lean_dec_ref(v_x_385_);
v___x_413_ = lean_apply_2(v_h__4_389_, v_a_411_, v_b_412_);
return v___x_413_;
}
default: 
{
lean_object* v_a_414_; lean_object* v_k_415_; lean_object* v___x_416_; 
lean_dec(v_h__9_394_);
lean_dec(v_h__8_393_);
lean_dec(v_h__7_392_);
lean_dec(v_h__6_391_);
lean_dec(v_h__4_389_);
lean_dec(v_h__3_388_);
lean_dec(v_h__2_387_);
lean_dec(v_h__1_386_);
v_a_414_ = lean_ctor_get(v_x_385_, 0);
lean_inc_ref(v_a_414_);
v_k_415_ = lean_ctor_get(v_x_385_, 1);
lean_inc(v_k_415_);
lean_dec_ref(v_x_385_);
v___x_416_ = lean_apply_2(v_h__5_390_, v_a_414_, v_k_415_);
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_417_, lean_object* v_h__1_418_, lean_object* v_h__2_419_, lean_object* v_h__3_420_){
_start:
{
switch(lean_obj_tag(v_a_417_))
{
case 0:
{
lean_object* v_k_421_; lean_object* v___x_422_; 
lean_dec(v_h__3_420_);
lean_dec(v_h__2_419_);
v_k_421_ = lean_ctor_get(v_a_417_, 0);
lean_inc(v_k_421_);
lean_dec_ref(v_a_417_);
v___x_422_ = lean_apply_1(v_h__1_418_, v_k_421_);
return v___x_422_;
}
case 3:
{
lean_object* v_i_423_; lean_object* v___x_424_; 
lean_dec(v_h__3_420_);
lean_dec(v_h__1_418_);
v_i_423_ = lean_ctor_get(v_a_417_, 0);
lean_inc(v_i_423_);
lean_dec_ref(v_a_417_);
v___x_424_ = lean_apply_1(v_h__2_419_, v_i_423_);
return v___x_424_;
}
default: 
{
lean_object* v___x_425_; 
lean_dec(v_h__2_419_);
lean_dec(v_h__1_418_);
v___x_425_ = lean_apply_3(v_h__3_420_, v_a_417_, lean_box(0), lean_box(0));
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_426_, lean_object* v_a_427_, lean_object* v_h__1_428_, lean_object* v_h__2_429_, lean_object* v_h__3_430_){
_start:
{
switch(lean_obj_tag(v_a_427_))
{
case 0:
{
lean_object* v_k_431_; lean_object* v___x_432_; 
lean_dec(v_h__3_430_);
lean_dec(v_h__2_429_);
v_k_431_ = lean_ctor_get(v_a_427_, 0);
lean_inc(v_k_431_);
lean_dec_ref(v_a_427_);
v___x_432_ = lean_apply_1(v_h__1_428_, v_k_431_);
return v___x_432_;
}
case 3:
{
lean_object* v_i_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_430_);
lean_dec(v_h__1_428_);
v_i_433_ = lean_ctor_get(v_a_427_, 0);
lean_inc(v_i_433_);
lean_dec_ref(v_a_427_);
v___x_434_ = lean_apply_1(v_h__2_429_, v_i_433_);
return v___x_434_;
}
default: 
{
lean_object* v___x_435_; 
lean_dec(v_h__2_429_);
lean_dec(v_h__1_428_);
v___x_435_ = lean_apply_3(v_h__3_430_, v_a_427_, lean_box(0), lean_box(0));
return v___x_435_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__cert(lean_object* v_lhs_436_, lean_object* v_rhs_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_438_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_436_);
v___x_439_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_437_);
v___x_440_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
lean_dec_ref(v___x_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__cert___boxed(lean_object* v_lhs_441_, lean_object* v_rhs_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_441_, v_rhs_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__nc__cert(lean_object* v_lhs_445_, lean_object* v_rhs_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_445_);
v___x_448_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_446_);
v___x_449_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_447_, v___x_448_);
lean_dec_ref(v___x_448_);
lean_dec_ref(v___x_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(lean_object* v_lhs_450_, lean_object* v_rhs_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_450_, v_rhs_451_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
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
