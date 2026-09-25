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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Mon_denote___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__2;
static lean_once_cell_t l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_CommRing_Expr_toPolyS___closed__3;
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
lean_dec_ref_known(v_x_3_, 1);
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
lean_dec_ref_known(v_x_3_, 1);
v___x_10_ = lean_apply_1(v_ofNat_8_, v_k_9_);
return v___x_10_;
}
case 3:
{
lean_object* v_i_11_; lean_object* v___x_12_; 
lean_dec_ref(v_inst_1_);
v_i_11_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_i_11_);
lean_dec_ref_known(v_x_3_, 1);
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
lean_dec_ref_known(v_x_3_, 2);
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
lean_dec_ref_known(v_x_3_, 2);
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
lean_dec_ref_known(v_x_3_, 2);
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
lean_dec_ref_known(v_x_49_, 1);
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
lean_dec_ref_known(v_x_49_, 1);
v___x_54_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_47_, v_k_53_);
return v___x_54_;
}
case 3:
{
lean_object* v_i_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_i_55_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_i_55_);
lean_dec_ref_known(v_x_49_, 1);
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
lean_dec_ref_known(v_x_49_, 2);
lean_inc_ref_n(v_inst_47_, 2);
v___x_60_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_a_58_);
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
lean_dec_ref_known(v_x_49_, 2);
lean_inc_ref_n(v_inst_47_, 2);
v___x_65_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_47_, v_ctx_48_, v_a_63_);
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
lean_dec_ref_known(v_x_49_, 2);
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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_x_88_, 1);
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
lean_dec_ref_known(v_x_88_, 2);
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
lean_dec_ref_known(v_x_88_, 2);
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
lean_dec_ref_known(v_x_88_, 2);
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
lean_dec_ref_known(v_x_88_, 2);
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
lean_dec_ref_known(v_x_121_, 1);
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
lean_dec_ref_known(v_x_121_, 1);
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
lean_dec_ref_known(v_x_121_, 1);
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
lean_dec_ref_known(v_x_121_, 1);
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
lean_dec_ref_known(v_x_121_, 1);
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
lean_dec_ref_known(v_x_121_, 2);
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
lean_dec_ref_known(v_x_121_, 2);
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
lean_dec_ref_known(v_x_121_, 2);
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
lean_dec_ref_known(v_x_121_, 2);
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
v___x_155_ = lean_unsigned_to_nat(1u);
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
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_nat_to_int(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object* v_x_163_){
_start:
{
switch(lean_obj_tag(v_x_163_))
{
case 0:
{
lean_object* v_k_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_173_; 
v_k_164_ = lean_ctor_get(v_x_163_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_173_ == 0)
{
v___x_166_ = v_x_163_;
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_k_164_);
lean_dec(v_x_163_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_173_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_168_ = lean_nat_abs(v_k_164_);
lean_dec(v_k_164_);
v___x_169_ = lean_nat_to_int(v___x_168_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_169_);
v___x_171_ = v___x_166_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
case 1:
{
lean_object* v_k_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_k_174_ = lean_ctor_get(v_x_163_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v_x_163_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_k_174_);
lean_dec(v_x_163_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_nat_to_int(v_k_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 0);
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_180_ = v___x_176_;
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
lean_object* v_i_183_; lean_object* v___x_184_; 
v_i_183_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_i_183_);
lean_dec_ref_known(v_x_163_, 1);
v___x_184_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_183_);
return v___x_184_;
}
case 5:
{
lean_object* v_a_185_; lean_object* v_b_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_a_185_ = lean_ctor_get(v_x_163_, 0);
lean_inc_ref(v_a_185_);
v_b_186_ = lean_ctor_get(v_x_163_, 1);
lean_inc_ref(v_b_186_);
lean_dec_ref_known(v_x_163_, 2);
v___x_187_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_185_);
v___x_188_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_186_);
v___x_189_ = l_Lean_Grind_CommRing_Poly_combine(v___x_187_, v___x_188_);
return v___x_189_;
}
case 7:
{
lean_object* v_a_190_; lean_object* v_b_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v_a_190_ = lean_ctor_get(v_x_163_, 0);
lean_inc_ref(v_a_190_);
v_b_191_ = lean_ctor_get(v_x_163_, 1);
lean_inc_ref(v_b_191_);
lean_dec_ref_known(v_x_163_, 2);
v___x_192_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_190_);
v___x_193_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_191_);
v___x_194_ = l_Lean_Grind_CommRing_Poly_mul(v___x_192_, v___x_193_);
return v___x_194_;
}
case 8:
{
lean_object* v_a_195_; lean_object* v_k_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_223_; 
v_a_195_ = lean_ctor_get(v_x_163_, 0);
v_k_196_ = lean_ctor_get(v_x_163_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_163_);
if (v_isSharedCheck_223_ == 0)
{
v___x_198_ = v_x_163_;
v_isShared_199_ = v_isSharedCheck_223_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_k_196_);
lean_inc(v_a_195_);
lean_dec(v_x_163_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_223_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_dec_eq(v_k_196_, v___x_200_);
if (v___x_201_ == 0)
{
switch(lean_obj_tag(v_a_195_))
{
case 0:
{
lean_object* v_k_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_212_; 
lean_del_object(v___x_198_);
v_k_202_ = lean_ctor_get(v_a_195_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_195_);
if (v_isSharedCheck_212_ == 0)
{
v___x_204_ = v_a_195_;
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_k_202_);
lean_dec(v_a_195_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_212_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_206_ = lean_nat_abs(v_k_202_);
lean_dec(v_k_202_);
v___x_207_ = lean_nat_to_int(v___x_206_);
v___x_208_ = l_Int_pow(v___x_207_, v_k_196_);
lean_dec(v_k_196_);
lean_dec(v___x_207_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_208_);
v___x_210_ = v___x_204_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
case 3:
{
lean_object* v_i_213_; lean_object* v___x_215_; 
v_i_213_ = lean_ctor_get(v_a_195_, 0);
lean_inc(v_i_213_);
lean_dec_ref_known(v_a_195_, 1);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 0);
lean_ctor_set(v___x_198_, 0, v_i_213_);
v___x_215_ = v___x_198_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_i_213_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v_k_196_);
v___x_215_ = v_reuseFailAlloc_219_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_box(0);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_217_);
return v___x_218_;
}
}
default: 
{
lean_object* v___x_220_; lean_object* v___x_221_; 
lean_del_object(v___x_198_);
v___x_220_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_195_);
v___x_221_ = l_Lean_Grind_CommRing_Poly_pow(v___x_220_, v_k_196_);
lean_dec(v_k_196_);
return v___x_221_;
}
}
}
else
{
lean_object* v___x_222_; 
lean_del_object(v___x_198_);
lean_dec(v_k_196_);
lean_dec_ref(v_a_195_);
v___x_222_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_222_;
}
}
}
default: 
{
lean_object* v___x_224_; 
lean_dec_ref(v_x_163_);
v___x_224_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object* v_x_225_){
_start:
{
switch(lean_obj_tag(v_x_225_))
{
case 0:
{
lean_object* v_k_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_235_; 
v_k_226_ = lean_ctor_get(v_x_225_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_235_ == 0)
{
v___x_228_ = v_x_225_;
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_k_226_);
lean_dec(v_x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = lean_nat_abs(v_k_226_);
lean_dec(v_k_226_);
v___x_231_ = lean_nat_to_int(v___x_230_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
case 1:
{
lean_object* v_k_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_k_236_ = lean_ctor_get(v_x_225_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v_x_225_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_k_236_);
lean_dec(v_x_225_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_nat_to_int(v_k_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 0);
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
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
lean_object* v_i_245_; lean_object* v___x_246_; 
v_i_245_ = lean_ctor_get(v_x_225_, 0);
lean_inc(v_i_245_);
lean_dec_ref_known(v_x_225_, 1);
v___x_246_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_245_);
return v___x_246_;
}
case 5:
{
lean_object* v_a_247_; lean_object* v_b_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_a_247_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_a_247_);
v_b_248_ = lean_ctor_get(v_x_225_, 1);
lean_inc_ref(v_b_248_);
lean_dec_ref_known(v_x_225_, 2);
v___x_249_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_247_);
v___x_250_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_248_);
v___x_251_ = l_Lean_Grind_CommRing_Poly_combine(v___x_249_, v___x_250_);
return v___x_251_;
}
case 7:
{
lean_object* v_a_252_; lean_object* v_b_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v_a_252_ = lean_ctor_get(v_x_225_, 0);
lean_inc_ref(v_a_252_);
v_b_253_ = lean_ctor_get(v_x_225_, 1);
lean_inc_ref(v_b_253_);
lean_dec_ref_known(v_x_225_, 2);
v___x_254_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_252_);
v___x_255_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_253_);
v___x_256_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_254_, v___x_255_);
return v___x_256_;
}
case 8:
{
lean_object* v_a_257_; lean_object* v_k_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_285_; 
v_a_257_ = lean_ctor_get(v_x_225_, 0);
v_k_258_ = lean_ctor_get(v_x_225_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_285_ == 0)
{
v___x_260_ = v_x_225_;
v_isShared_261_ = v_isSharedCheck_285_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_k_258_);
lean_inc(v_a_257_);
lean_dec(v_x_225_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_285_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v_k_258_, v___x_262_);
if (v___x_263_ == 0)
{
switch(lean_obj_tag(v_a_257_))
{
case 0:
{
lean_object* v_k_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_274_; 
lean_del_object(v___x_260_);
v_k_264_ = lean_ctor_get(v_a_257_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_257_);
if (v_isSharedCheck_274_ == 0)
{
v___x_266_ = v_a_257_;
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_k_264_);
lean_dec(v_a_257_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_268_ = lean_nat_abs(v_k_264_);
lean_dec(v_k_264_);
v___x_269_ = lean_nat_to_int(v___x_268_);
v___x_270_ = l_Int_pow(v___x_269_, v_k_258_);
lean_dec(v_k_258_);
lean_dec(v___x_269_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_272_ = v___x_266_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
case 3:
{
lean_object* v_i_275_; lean_object* v___x_277_; 
v_i_275_ = lean_ctor_get(v_a_257_, 0);
lean_inc(v_i_275_);
lean_dec_ref_known(v_a_257_, 1);
if (v_isShared_261_ == 0)
{
lean_ctor_set_tag(v___x_260_, 0);
lean_ctor_set(v___x_260_, 0, v_i_275_);
v___x_277_ = v___x_260_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_i_275_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_k_258_);
v___x_277_ = v_reuseFailAlloc_281_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_279_);
return v___x_280_;
}
}
default: 
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_del_object(v___x_260_);
v___x_282_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_257_);
v___x_283_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_282_, v_k_258_);
lean_dec(v_k_258_);
return v___x_283_;
}
}
}
else
{
lean_object* v___x_284_; 
lean_del_object(v___x_260_);
lean_dec(v_k_258_);
lean_dec_ref(v_a_257_);
v___x_284_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_284_;
}
}
}
default: 
{
lean_object* v___x_286_; 
lean_dec_ref(v_x_225_);
v___x_286_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_287_, lean_object* v_k_288_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_291_ = lean_int_dec_lt(v_k_288_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v_ofNat_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_ofNat_292_ = lean_ctor_get(v_inst_287_, 3);
lean_inc(v_ofNat_292_);
lean_dec_ref(v_inst_287_);
v___x_293_ = lean_nat_abs(v_k_288_);
v___x_294_ = lean_apply_1(v_ofNat_292_, v___x_293_);
return v___x_294_;
}
else
{
lean_object* v_ofNat_295_; lean_object* v___x_296_; 
v_ofNat_295_ = lean_ctor_get(v_inst_287_, 3);
lean_inc(v_ofNat_295_);
lean_dec_ref(v_inst_287_);
v___x_296_ = lean_apply_1(v_ofNat_295_, v___x_289_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_297_, lean_object* v_k_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_297_, v_k_298_);
lean_dec(v_k_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_300_, lean_object* v_inst_301_, lean_object* v_k_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_301_, v_k_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_304_, lean_object* v_inst_305_, lean_object* v_k_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_304_, v_inst_305_, v_k_306_);
lean_dec(v_k_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_308_, lean_object* v_ctx_309_, lean_object* v_p_310_){
_start:
{
if (lean_obj_tag(v_p_310_) == 0)
{
lean_object* v_k_311_; lean_object* v___x_312_; 
v_k_311_ = lean_ctor_get(v_p_310_, 0);
lean_inc(v_k_311_);
lean_dec_ref_known(v_p_310_, 1);
v___x_312_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_308_, v_k_311_);
lean_dec(v_k_311_);
return v___x_312_;
}
else
{
lean_object* v_toAdd_313_; lean_object* v_toMul_314_; lean_object* v_k_315_; lean_object* v_v_316_; lean_object* v_p_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_toAdd_313_ = lean_ctor_get(v_inst_308_, 0);
lean_inc(v_toAdd_313_);
v_toMul_314_ = lean_ctor_get(v_inst_308_, 1);
v_k_315_ = lean_ctor_get(v_p_310_, 0);
lean_inc(v_k_315_);
v_v_316_ = lean_ctor_get(v_p_310_, 1);
lean_inc(v_v_316_);
v_p_317_ = lean_ctor_get(v_p_310_, 2);
lean_inc_ref(v_p_317_);
lean_dec_ref_known(v_p_310_, 3);
lean_inc_ref_n(v_inst_308_, 2);
v___x_318_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_308_, v_k_315_);
lean_dec(v_k_315_);
v___x_319_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_308_, v_ctx_309_, v_v_316_);
lean_inc(v_toMul_314_);
v___x_320_ = lean_apply_2(v_toMul_314_, v___x_318_, v___x_319_);
v___x_321_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_308_, v_ctx_309_, v_p_317_);
v___x_322_ = lean_apply_2(v_toAdd_313_, v___x_320_, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_323_, lean_object* v_ctx_324_, lean_object* v_p_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_323_, v_ctx_324_, v_p_325_);
lean_dec_ref(v_ctx_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_327_, lean_object* v_inst_328_, lean_object* v_ctx_329_, lean_object* v_p_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_328_, v_ctx_329_, v_p_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_332_, lean_object* v_inst_333_, lean_object* v_ctx_334_, lean_object* v_p_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_332_, v_inst_333_, v_ctx_334_, v_p_335_);
lean_dec_ref(v_ctx_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(lean_object* v_p_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_p_337_) == 0)
{
lean_object* v_k_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_339_);
v_k_340_ = lean_ctor_get(v_p_337_, 0);
lean_inc(v_k_340_);
lean_dec_ref_known(v_p_337_, 1);
v___x_341_ = lean_apply_1(v_h__1_338_, v_k_340_);
return v___x_341_;
}
else
{
lean_object* v_k_342_; lean_object* v_v_343_; lean_object* v_p_344_; lean_object* v___x_345_; 
lean_dec(v_h__1_338_);
v_k_342_ = lean_ctor_get(v_p_337_, 0);
lean_inc(v_k_342_);
v_v_343_ = lean_ctor_get(v_p_337_, 1);
lean_inc(v_v_343_);
v_p_344_ = lean_ctor_get(v_p_337_, 2);
lean_inc_ref(v_p_344_);
lean_dec_ref_known(v_p_337_, 3);
v___x_345_ = lean_apply_3(v_h__2_339_, v_k_342_, v_v_343_, v_p_344_);
return v___x_345_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(lean_object* v_motive_346_, lean_object* v_p_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_){
_start:
{
if (lean_obj_tag(v_p_347_) == 0)
{
lean_object* v_k_350_; lean_object* v___x_351_; 
lean_dec(v_h__2_349_);
v_k_350_ = lean_ctor_get(v_p_347_, 0);
lean_inc(v_k_350_);
lean_dec_ref_known(v_p_347_, 1);
v___x_351_ = lean_apply_1(v_h__1_348_, v_k_350_);
return v___x_351_;
}
else
{
lean_object* v_k_352_; lean_object* v_v_353_; lean_object* v_p_354_; lean_object* v___x_355_; 
lean_dec(v_h__1_348_);
v_k_352_ = lean_ctor_get(v_p_347_, 0);
lean_inc(v_k_352_);
v_v_353_ = lean_ctor_get(v_p_347_, 1);
lean_inc(v_v_353_);
v_p_354_ = lean_ctor_get(v_p_347_, 2);
lean_inc_ref(v_p_354_);
lean_dec_ref_known(v_p_347_, 3);
v___x_355_ = lean_apply_3(v_h__2_349_, v_k_352_, v_v_353_, v_p_354_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_, lean_object* v_h__3_359_, lean_object* v_h__4_360_, lean_object* v_h__5_361_, lean_object* v_h__6_362_, lean_object* v_h__7_363_, lean_object* v_h__8_364_, lean_object* v_h__9_365_){
_start:
{
switch(lean_obj_tag(v_x_356_))
{
case 0:
{
lean_object* v_k_366_; lean_object* v___x_367_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
v_k_366_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_k_366_);
lean_dec_ref_known(v_x_356_, 1);
v___x_367_ = lean_apply_1(v_h__1_357_, v_k_366_);
return v___x_367_;
}
case 1:
{
lean_object* v_k_368_; lean_object* v___x_369_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_k_368_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_k_368_);
lean_dec_ref_known(v_x_356_, 1);
v___x_369_ = lean_apply_1(v_h__6_362_, v_k_368_);
return v___x_369_;
}
case 2:
{
lean_object* v_k_370_; lean_object* v___x_371_; 
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_k_370_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_k_370_);
lean_dec_ref_known(v_x_356_, 1);
v___x_371_ = lean_apply_1(v_h__9_365_, v_k_370_);
return v___x_371_;
}
case 3:
{
lean_object* v_i_372_; lean_object* v___x_373_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__1_357_);
v_i_372_ = lean_ctor_get(v_x_356_, 0);
lean_inc(v_i_372_);
lean_dec_ref_known(v_x_356_, 1);
v___x_373_ = lean_apply_1(v_h__2_358_, v_i_372_);
return v___x_373_;
}
case 4:
{
lean_object* v_a_374_; lean_object* v___x_375_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_a_374_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_a_374_);
lean_dec_ref_known(v_x_356_, 1);
v___x_375_ = lean_apply_1(v_h__8_364_, v_a_374_);
return v___x_375_;
}
case 5:
{
lean_object* v_a_376_; lean_object* v_b_377_; lean_object* v___x_378_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_a_376_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_a_376_);
v_b_377_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_b_377_);
lean_dec_ref_known(v_x_356_, 2);
v___x_378_ = lean_apply_2(v_h__3_359_, v_a_376_, v_b_377_);
return v___x_378_;
}
case 6:
{
lean_object* v_a_379_; lean_object* v_b_380_; lean_object* v___x_381_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_a_379_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_a_379_);
v_b_380_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_b_380_);
lean_dec_ref_known(v_x_356_, 2);
v___x_381_ = lean_apply_2(v_h__7_363_, v_a_379_, v_b_380_);
return v___x_381_;
}
case 7:
{
lean_object* v_a_382_; lean_object* v_b_383_; lean_object* v___x_384_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__5_361_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_a_382_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_a_382_);
v_b_383_ = lean_ctor_get(v_x_356_, 1);
lean_inc_ref(v_b_383_);
lean_dec_ref_known(v_x_356_, 2);
v___x_384_ = lean_apply_2(v_h__4_360_, v_a_382_, v_b_383_);
return v___x_384_;
}
default: 
{
lean_object* v_a_385_; lean_object* v_k_386_; lean_object* v___x_387_; 
lean_dec(v_h__9_365_);
lean_dec(v_h__8_364_);
lean_dec(v_h__7_363_);
lean_dec(v_h__6_362_);
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
v_a_385_ = lean_ctor_get(v_x_356_, 0);
lean_inc_ref(v_a_385_);
v_k_386_ = lean_ctor_get(v_x_356_, 1);
lean_inc(v_k_386_);
lean_dec_ref_known(v_x_356_, 2);
v___x_387_ = lean_apply_2(v_h__5_361_, v_a_385_, v_k_386_);
return v___x_387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_388_, lean_object* v_x_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_, lean_object* v_h__3_392_, lean_object* v_h__4_393_, lean_object* v_h__5_394_, lean_object* v_h__6_395_, lean_object* v_h__7_396_, lean_object* v_h__8_397_, lean_object* v_h__9_398_){
_start:
{
switch(lean_obj_tag(v_x_389_))
{
case 0:
{
lean_object* v_k_399_; lean_object* v___x_400_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
v_k_399_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_k_399_);
lean_dec_ref_known(v_x_389_, 1);
v___x_400_ = lean_apply_1(v_h__1_390_, v_k_399_);
return v___x_400_;
}
case 1:
{
lean_object* v_k_401_; lean_object* v___x_402_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_k_401_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_k_401_);
lean_dec_ref_known(v_x_389_, 1);
v___x_402_ = lean_apply_1(v_h__6_395_, v_k_401_);
return v___x_402_;
}
case 2:
{
lean_object* v_k_403_; lean_object* v___x_404_; 
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_k_403_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_k_403_);
lean_dec_ref_known(v_x_389_, 1);
v___x_404_ = lean_apply_1(v_h__9_398_, v_k_403_);
return v___x_404_;
}
case 3:
{
lean_object* v_i_405_; lean_object* v___x_406_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__1_390_);
v_i_405_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_i_405_);
lean_dec_ref_known(v_x_389_, 1);
v___x_406_ = lean_apply_1(v_h__2_391_, v_i_405_);
return v___x_406_;
}
case 4:
{
lean_object* v_a_407_; lean_object* v___x_408_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_a_407_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_a_407_);
lean_dec_ref_known(v_x_389_, 1);
v___x_408_ = lean_apply_1(v_h__8_397_, v_a_407_);
return v___x_408_;
}
case 5:
{
lean_object* v_a_409_; lean_object* v_b_410_; lean_object* v___x_411_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_a_409_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_a_409_);
v_b_410_ = lean_ctor_get(v_x_389_, 1);
lean_inc_ref(v_b_410_);
lean_dec_ref_known(v_x_389_, 2);
v___x_411_ = lean_apply_2(v_h__3_392_, v_a_409_, v_b_410_);
return v___x_411_;
}
case 6:
{
lean_object* v_a_412_; lean_object* v_b_413_; lean_object* v___x_414_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_a_412_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_a_412_);
v_b_413_ = lean_ctor_get(v_x_389_, 1);
lean_inc_ref(v_b_413_);
lean_dec_ref_known(v_x_389_, 2);
v___x_414_ = lean_apply_2(v_h__7_396_, v_a_412_, v_b_413_);
return v___x_414_;
}
case 7:
{
lean_object* v_a_415_; lean_object* v_b_416_; lean_object* v___x_417_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__5_394_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_a_415_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_a_415_);
v_b_416_ = lean_ctor_get(v_x_389_, 1);
lean_inc_ref(v_b_416_);
lean_dec_ref_known(v_x_389_, 2);
v___x_417_ = lean_apply_2(v_h__4_393_, v_a_415_, v_b_416_);
return v___x_417_;
}
default: 
{
lean_object* v_a_418_; lean_object* v_k_419_; lean_object* v___x_420_; 
lean_dec(v_h__9_398_);
lean_dec(v_h__8_397_);
lean_dec(v_h__7_396_);
lean_dec(v_h__6_395_);
lean_dec(v_h__4_393_);
lean_dec(v_h__3_392_);
lean_dec(v_h__2_391_);
lean_dec(v_h__1_390_);
v_a_418_ = lean_ctor_get(v_x_389_, 0);
lean_inc_ref(v_a_418_);
v_k_419_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_k_419_);
lean_dec_ref_known(v_x_389_, 2);
v___x_420_ = lean_apply_2(v_h__5_394_, v_a_418_, v_k_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_421_, lean_object* v_h__1_422_, lean_object* v_h__2_423_, lean_object* v_h__3_424_){
_start:
{
switch(lean_obj_tag(v_a_421_))
{
case 0:
{
lean_object* v_k_425_; lean_object* v___x_426_; 
lean_dec(v_h__3_424_);
lean_dec(v_h__2_423_);
v_k_425_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_k_425_);
lean_dec_ref_known(v_a_421_, 1);
v___x_426_ = lean_apply_1(v_h__1_422_, v_k_425_);
return v___x_426_;
}
case 3:
{
lean_object* v_i_427_; lean_object* v___x_428_; 
lean_dec(v_h__3_424_);
lean_dec(v_h__1_422_);
v_i_427_ = lean_ctor_get(v_a_421_, 0);
lean_inc(v_i_427_);
lean_dec_ref_known(v_a_421_, 1);
v___x_428_ = lean_apply_1(v_h__2_423_, v_i_427_);
return v___x_428_;
}
default: 
{
lean_object* v___x_429_; 
lean_dec(v_h__2_423_);
lean_dec(v_h__1_422_);
v___x_429_ = lean_apply_3(v_h__3_424_, v_a_421_, lean_box(0), lean_box(0));
return v___x_429_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_430_, lean_object* v_a_431_, lean_object* v_h__1_432_, lean_object* v_h__2_433_, lean_object* v_h__3_434_){
_start:
{
switch(lean_obj_tag(v_a_431_))
{
case 0:
{
lean_object* v_k_435_; lean_object* v___x_436_; 
lean_dec(v_h__3_434_);
lean_dec(v_h__2_433_);
v_k_435_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_k_435_);
lean_dec_ref_known(v_a_431_, 1);
v___x_436_ = lean_apply_1(v_h__1_432_, v_k_435_);
return v___x_436_;
}
case 3:
{
lean_object* v_i_437_; lean_object* v___x_438_; 
lean_dec(v_h__3_434_);
lean_dec(v_h__1_432_);
v_i_437_ = lean_ctor_get(v_a_431_, 0);
lean_inc(v_i_437_);
lean_dec_ref_known(v_a_431_, 1);
v___x_438_ = lean_apply_1(v_h__2_433_, v_i_437_);
return v___x_438_;
}
default: 
{
lean_object* v___x_439_; 
lean_dec(v_h__2_433_);
lean_dec(v_h__1_432_);
v___x_439_ = lean_apply_3(v_h__3_434_, v_a_431_, lean_box(0), lean_box(0));
return v___x_439_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__cert(lean_object* v_lhs_440_, lean_object* v_rhs_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_440_);
v___x_443_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_441_);
v___x_444_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
lean_dec_ref(v___x_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__cert___boxed(lean_object* v_lhs_445_, lean_object* v_rhs_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_445_, v_rhs_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__nc__cert(lean_object* v_lhs_449_, lean_object* v_rhs_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_451_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_449_);
v___x_452_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_450_);
v___x_453_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_451_, v___x_452_);
lean_dec_ref(v___x_452_);
lean_dec_ref(v___x_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(lean_object* v_lhs_454_, lean_object* v_rhs_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_454_, v_rhs_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Ring_CommSolver(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
