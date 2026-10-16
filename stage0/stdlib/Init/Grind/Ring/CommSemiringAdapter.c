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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(lean_object* v_a_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_nat_to_int(v_a_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_to_int(v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__0, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_nat_to_int(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS(lean_object* v_x_98_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
lean_object* v_k_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_k_99_ = lean_ctor_get(v_x_98_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v_x_98_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_k_99_);
lean_dec(v_x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = lean_nat_abs(v_k_99_);
lean_dec(v_k_99_);
v___x_104_ = lean_nat_to_int(v___x_103_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_104_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
case 1:
{
lean_object* v_k_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_117_; 
v_k_109_ = lean_ctor_get(v_x_98_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_117_ == 0)
{
v___x_111_ = v_x_98_;
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_k_109_);
lean_dec(v_x_98_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_117_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_113_ = lean_nat_to_int(v_k_109_);
if (v_isShared_112_ == 0)
{
lean_ctor_set_tag(v___x_111_, 0);
lean_ctor_set(v___x_111_, 0, v___x_113_);
v___x_115_ = v___x_111_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
case 3:
{
lean_object* v_i_118_; lean_object* v___x_119_; 
v_i_118_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_i_118_);
lean_dec_ref_known(v_x_98_, 1);
v___x_119_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_118_);
return v___x_119_;
}
case 5:
{
lean_object* v_a_120_; lean_object* v_b_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_a_120_ = lean_ctor_get(v_x_98_, 0);
lean_inc_ref(v_a_120_);
v_b_121_ = lean_ctor_get(v_x_98_, 1);
lean_inc_ref(v_b_121_);
lean_dec_ref_known(v_x_98_, 2);
v___x_122_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_120_);
v___x_123_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_121_);
v___x_124_ = l_Lean_Grind_CommRing_Poly_combine(v___x_122_, v___x_123_);
return v___x_124_;
}
case 7:
{
lean_object* v_a_125_; lean_object* v_b_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_a_125_ = lean_ctor_get(v_x_98_, 0);
lean_inc_ref(v_a_125_);
v_b_126_ = lean_ctor_get(v_x_98_, 1);
lean_inc_ref(v_b_126_);
lean_dec_ref_known(v_x_98_, 2);
v___x_127_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_125_);
v___x_128_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_126_);
v___x_129_ = l_Lean_Grind_CommRing_Poly_mul(v___x_127_, v___x_128_);
return v___x_129_;
}
case 8:
{
lean_object* v_a_130_; lean_object* v_k_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_158_; 
v_a_130_ = lean_ctor_get(v_x_98_, 0);
v_k_131_ = lean_ctor_get(v_x_98_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_98_);
if (v_isSharedCheck_158_ == 0)
{
v___x_133_ = v_x_98_;
v_isShared_134_ = v_isSharedCheck_158_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_k_131_);
lean_inc(v_a_130_);
lean_dec(v_x_98_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_158_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_nat_dec_eq(v_k_131_, v___x_135_);
if (v___x_136_ == 0)
{
switch(lean_obj_tag(v_a_130_))
{
case 0:
{
lean_object* v_k_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
lean_del_object(v___x_133_);
v_k_137_ = lean_ctor_get(v_a_130_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v_a_130_);
if (v_isSharedCheck_147_ == 0)
{
v___x_139_ = v_a_130_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_k_137_);
lean_dec(v_a_130_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_141_ = lean_nat_abs(v_k_137_);
lean_dec(v_k_137_);
v___x_142_ = lean_nat_to_int(v___x_141_);
v___x_143_ = l_Int_pow(v___x_142_, v_k_131_);
lean_dec(v_k_131_);
lean_dec(v___x_142_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 0, v___x_143_);
v___x_145_ = v___x_139_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
case 3:
{
lean_object* v_i_148_; lean_object* v___x_150_; 
v_i_148_ = lean_ctor_get(v_a_130_, 0);
lean_inc(v_i_148_);
lean_dec_ref_known(v_a_130_, 1);
if (v_isShared_134_ == 0)
{
lean_ctor_set_tag(v___x_133_, 0);
lean_ctor_set(v___x_133_, 0, v_i_148_);
v___x_150_ = v___x_133_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_i_148_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v_k_131_);
v___x_150_ = v_reuseFailAlloc_154_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_152_);
return v___x_153_;
}
}
default: 
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_del_object(v___x_133_);
v___x_155_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_130_);
v___x_156_ = l_Lean_Grind_CommRing_Poly_pow(v___x_155_, v_k_131_);
lean_dec(v_k_131_);
return v___x_156_;
}
}
}
else
{
lean_object* v___x_157_; 
lean_del_object(v___x_133_);
lean_dec(v_k_131_);
lean_dec_ref(v_a_130_);
v___x_157_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_157_;
}
}
}
default: 
{
lean_object* v___x_159_; 
lean_dec_ref(v_x_98_);
v___x_159_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_toPolyS__nc(lean_object* v_x_160_){
_start:
{
switch(lean_obj_tag(v_x_160_))
{
case 0:
{
lean_object* v_k_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_170_; 
v_k_161_ = lean_ctor_get(v_x_160_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_170_ == 0)
{
v___x_163_ = v_x_160_;
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_k_161_);
lean_dec(v_x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_170_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_165_ = lean_nat_abs(v_k_161_);
lean_dec(v_k_161_);
v___x_166_ = lean_nat_to_int(v___x_165_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_166_);
v___x_168_ = v___x_163_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
case 1:
{
lean_object* v_k_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_k_171_ = lean_ctor_get(v_x_160_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v_x_160_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_k_171_);
lean_dec(v_x_160_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_nat_to_int(v_k_171_);
if (v_isShared_174_ == 0)
{
lean_ctor_set_tag(v___x_173_, 0);
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
case 3:
{
lean_object* v_i_180_; lean_object* v___x_181_; 
v_i_180_ = lean_ctor_get(v_x_160_, 0);
lean_inc(v_i_180_);
lean_dec_ref_known(v_x_160_, 1);
v___x_181_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_180_);
return v___x_181_;
}
case 5:
{
lean_object* v_a_182_; lean_object* v_b_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_a_182_ = lean_ctor_get(v_x_160_, 0);
lean_inc_ref(v_a_182_);
v_b_183_ = lean_ctor_get(v_x_160_, 1);
lean_inc_ref(v_b_183_);
lean_dec_ref_known(v_x_160_, 2);
v___x_184_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_182_);
v___x_185_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_183_);
v___x_186_ = l_Lean_Grind_CommRing_Poly_combine(v___x_184_, v___x_185_);
return v___x_186_;
}
case 7:
{
lean_object* v_a_187_; lean_object* v_b_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_a_187_ = lean_ctor_get(v_x_160_, 0);
lean_inc_ref(v_a_187_);
v_b_188_ = lean_ctor_get(v_x_160_, 1);
lean_inc_ref(v_b_188_);
lean_dec_ref_known(v_x_160_, 2);
v___x_189_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_187_);
v___x_190_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_188_);
v___x_191_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_189_, v___x_190_);
return v___x_191_;
}
case 8:
{
lean_object* v_a_192_; lean_object* v_k_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_220_; 
v_a_192_ = lean_ctor_get(v_x_160_, 0);
v_k_193_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_220_ == 0)
{
v___x_195_ = v_x_160_;
v_isShared_196_ = v_isSharedCheck_220_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_k_193_);
lean_inc(v_a_192_);
lean_dec(v_x_160_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_220_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_nat_dec_eq(v_k_193_, v___x_197_);
if (v___x_198_ == 0)
{
switch(lean_obj_tag(v_a_192_))
{
case 0:
{
lean_object* v_k_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_209_; 
lean_del_object(v___x_195_);
v_k_199_ = lean_ctor_get(v_a_192_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_209_ == 0)
{
v___x_201_ = v_a_192_;
v_isShared_202_ = v_isSharedCheck_209_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_k_199_);
lean_dec(v_a_192_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_209_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
v___x_203_ = lean_nat_abs(v_k_199_);
lean_dec(v_k_199_);
v___x_204_ = lean_nat_to_int(v___x_203_);
v___x_205_ = l_Int_pow(v___x_204_, v_k_193_);
lean_dec(v_k_193_);
lean_dec(v___x_204_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_205_);
v___x_207_ = v___x_201_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_205_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
case 3:
{
lean_object* v_i_210_; lean_object* v___x_212_; 
v_i_210_ = lean_ctor_get(v_a_192_, 0);
lean_inc(v_i_210_);
lean_dec_ref_known(v_a_192_, 1);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 0);
lean_ctor_set(v___x_195_, 0, v_i_210_);
v___x_212_ = v___x_195_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_i_210_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_k_193_);
v___x_212_ = v_reuseFailAlloc_216_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_214_);
return v___x_215_;
}
}
default: 
{
lean_object* v___x_217_; lean_object* v___x_218_; 
lean_del_object(v___x_195_);
v___x_217_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_192_);
v___x_218_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_217_, v_k_193_);
lean_dec(v_k_193_);
return v___x_218_;
}
}
}
else
{
lean_object* v___x_219_; 
lean_del_object(v___x_195_);
lean_dec(v_k_193_);
lean_dec_ref(v_a_192_);
v___x_219_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__1, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1);
return v___x_219_;
}
}
}
default: 
{
lean_object* v___x_221_; 
lean_dec_ref(v_x_160_);
v___x_221_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__3, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__3_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__3);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_222_, lean_object* v_k_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_226_ = lean_int_dec_lt(v_k_223_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v_ofNat_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_ofNat_227_ = lean_ctor_get(v_inst_222_, 3);
lean_inc(v_ofNat_227_);
lean_dec_ref(v_inst_222_);
v___x_228_ = lean_nat_abs(v_k_223_);
v___x_229_ = lean_apply_1(v_ofNat_227_, v___x_228_);
return v___x_229_;
}
else
{
lean_object* v_ofNat_230_; lean_object* v___x_231_; 
v_ofNat_230_ = lean_ctor_get(v_inst_222_, 3);
lean_inc(v_ofNat_230_);
lean_dec_ref(v_inst_222_);
v___x_231_ = lean_apply_1(v_ofNat_230_, v___x_224_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_232_, lean_object* v_k_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_232_, v_k_233_);
lean_dec(v_k_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_k_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_236_, v_k_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_239_, lean_object* v_inst_240_, lean_object* v_k_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_239_, v_inst_240_, v_k_241_);
lean_dec(v_k_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_243_, lean_object* v_ctx_244_, lean_object* v_p_245_){
_start:
{
if (lean_obj_tag(v_p_245_) == 0)
{
lean_object* v_k_246_; lean_object* v___x_247_; 
v_k_246_ = lean_ctor_get(v_p_245_, 0);
lean_inc(v_k_246_);
lean_dec_ref_known(v_p_245_, 1);
v___x_247_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_243_, v_k_246_);
lean_dec(v_k_246_);
return v___x_247_;
}
else
{
lean_object* v_toAdd_248_; lean_object* v_toMul_249_; lean_object* v_k_250_; lean_object* v_v_251_; lean_object* v_p_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_toAdd_248_ = lean_ctor_get(v_inst_243_, 0);
lean_inc(v_toAdd_248_);
v_toMul_249_ = lean_ctor_get(v_inst_243_, 1);
v_k_250_ = lean_ctor_get(v_p_245_, 0);
lean_inc(v_k_250_);
v_v_251_ = lean_ctor_get(v_p_245_, 1);
lean_inc(v_v_251_);
v_p_252_ = lean_ctor_get(v_p_245_, 2);
lean_inc_ref(v_p_252_);
lean_dec_ref_known(v_p_245_, 3);
lean_inc_ref_n(v_inst_243_, 2);
v___x_253_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_243_, v_k_250_);
lean_dec(v_k_250_);
v___x_254_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_243_, v_ctx_244_, v_v_251_);
lean_inc(v_toMul_249_);
v___x_255_ = lean_apply_2(v_toMul_249_, v___x_253_, v___x_254_);
v___x_256_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_243_, v_ctx_244_, v_p_252_);
v___x_257_ = lean_apply_2(v_toAdd_248_, v___x_255_, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_258_, lean_object* v_ctx_259_, lean_object* v_p_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_258_, v_ctx_259_, v_p_260_);
lean_dec_ref(v_ctx_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_262_, lean_object* v_inst_263_, lean_object* v_ctx_264_, lean_object* v_p_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_263_, v_ctx_264_, v_p_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_ctx_269_, lean_object* v_p_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_267_, v_inst_268_, v_ctx_269_, v_p_270_);
lean_dec_ref(v_ctx_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter___redArg(lean_object* v_p_272_, lean_object* v_h__1_273_, lean_object* v_h__2_274_){
_start:
{
if (lean_obj_tag(v_p_272_) == 0)
{
lean_object* v_k_275_; lean_object* v___x_276_; 
lean_dec(v_h__2_274_);
v_k_275_ = lean_ctor_get(v_p_272_, 0);
lean_inc(v_k_275_);
lean_dec_ref_known(v_p_272_, 1);
v___x_276_ = lean_apply_1(v_h__1_273_, v_k_275_);
return v___x_276_;
}
else
{
lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_p_279_; lean_object* v___x_280_; 
lean_dec(v_h__1_273_);
v_k_277_ = lean_ctor_get(v_p_272_, 0);
lean_inc(v_k_277_);
v_v_278_ = lean_ctor_get(v_p_272_, 1);
lean_inc(v_v_278_);
v_p_279_ = lean_ctor_get(v_p_272_, 2);
lean_inc_ref(v_p_279_);
lean_dec_ref_known(v_p_272_, 3);
v___x_280_ = lean_apply_3(v_h__2_274_, v_k_277_, v_v_278_, v_p_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denote_match__1_splitter(lean_object* v_motive_281_, lean_object* v_p_282_, lean_object* v_h__1_283_, lean_object* v_h__2_284_){
_start:
{
if (lean_obj_tag(v_p_282_) == 0)
{
lean_object* v_k_285_; lean_object* v___x_286_; 
lean_dec(v_h__2_284_);
v_k_285_ = lean_ctor_get(v_p_282_, 0);
lean_inc(v_k_285_);
lean_dec_ref_known(v_p_282_, 1);
v___x_286_ = lean_apply_1(v_h__1_283_, v_k_285_);
return v___x_286_;
}
else
{
lean_object* v_k_287_; lean_object* v_v_288_; lean_object* v_p_289_; lean_object* v___x_290_; 
lean_dec(v_h__1_283_);
v_k_287_ = lean_ctor_get(v_p_282_, 0);
lean_inc(v_k_287_);
v_v_288_ = lean_ctor_get(v_p_282_, 1);
lean_inc(v_v_288_);
v_p_289_ = lean_ctor_get(v_p_282_, 2);
lean_inc_ref(v_p_289_);
lean_dec_ref_known(v_p_282_, 3);
v___x_290_ = lean_apply_3(v_h__2_284_, v_k_287_, v_v_288_, v_p_289_);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(uint8_t v_x_291_, lean_object* v_h__1_292_, lean_object* v_h__2_293_, lean_object* v_h__3_294_){
_start:
{
switch(v_x_291_)
{
case 0:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec(v_h__2_293_);
lean_dec(v_h__1_292_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_apply_1(v_h__3_294_, v___x_295_);
return v___x_296_;
}
case 1:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
lean_dec(v_h__3_294_);
lean_dec(v_h__2_293_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_apply_1(v_h__1_292_, v___x_297_);
return v___x_298_;
}
default: 
{
lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec(v_h__3_294_);
lean_dec(v_h__1_292_);
v___x_299_ = lean_box(0);
v___x_300_ = lean_apply_1(v_h__2_293_, v___x_299_);
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg___boxed(lean_object* v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_, lean_object* v_h__3_304_){
_start:
{
uint8_t v_x_33__boxed_305_; lean_object* v_res_306_; 
v_x_33__boxed_305_ = lean_unbox(v_x_301_);
v_res_306_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___redArg(v_x_33__boxed_305_, v_h__1_302_, v_h__2_303_, v_h__3_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(lean_object* v_motive_307_, uint8_t v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
switch(v_x_308_)
{
case 0:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_h__2_310_);
lean_dec(v_h__1_309_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v_h__3_311_, v___x_312_);
return v___x_313_;
}
case 1:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__2_310_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_apply_1(v_h__1_309_, v___x_314_);
return v___x_315_;
}
default: 
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__1_309_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_apply_1(v_h__2_310_, v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter___boxed(lean_object* v_motive_318_, lean_object* v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_, lean_object* v_h__3_322_){
_start:
{
uint8_t v_x_48__boxed_323_; lean_object* v_res_324_; 
v_x_48__boxed_323_ = lean_unbox(v_x_319_);
v_res_324_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_insert_go_match__1_splitter(v_motive_318_, v_x_48__boxed_323_, v_h__1_320_, v_h__2_321_, v_h__3_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(lean_object* v_fuel_325_, lean_object* v_h__1_326_, lean_object* v_h__2_327_){
_start:
{
lean_object* v_zero_328_; uint8_t v_isZero_329_; 
v_zero_328_ = lean_unsigned_to_nat(0u);
v_isZero_329_ = lean_nat_dec_eq(v_fuel_325_, v_zero_328_);
if (v_isZero_329_ == 1)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__2_327_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__1_326_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v_one_332_; lean_object* v_n_333_; lean_object* v___x_334_; 
lean_dec(v_h__1_326_);
v_one_332_ = lean_unsigned_to_nat(1u);
v_n_333_ = lean_nat_sub(v_fuel_325_, v_one_332_);
v___x_334_ = lean_apply_1(v_h__2_327_, v_n_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg___boxed(lean_object* v_fuel_335_, lean_object* v_h__1_336_, lean_object* v_h__2_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___redArg(v_fuel_335_, v_h__1_336_, v_h__2_337_);
lean_dec(v_fuel_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(lean_object* v_motive_339_, lean_object* v_fuel_340_, lean_object* v_h__1_341_, lean_object* v_h__2_342_){
_start:
{
lean_object* v_zero_343_; uint8_t v_isZero_344_; 
v_zero_343_ = lean_unsigned_to_nat(0u);
v_isZero_344_ = lean_nat_dec_eq(v_fuel_340_, v_zero_343_);
if (v_isZero_344_ == 1)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_h__2_342_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_1(v_h__1_341_, v___x_345_);
return v___x_346_;
}
else
{
lean_object* v_one_347_; lean_object* v_n_348_; lean_object* v___x_349_; 
lean_dec(v_h__1_341_);
v_one_347_ = lean_unsigned_to_nat(1u);
v_n_348_ = lean_nat_sub(v_fuel_340_, v_one_347_);
v___x_349_ = lean_apply_1(v_h__2_342_, v_n_348_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter___boxed(lean_object* v_motive_350_, lean_object* v_fuel_351_, lean_object* v_h__1_352_, lean_object* v_h__2_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Mon_mul_go_match__3_splitter(v_motive_350_, v_fuel_351_, v_h__1_352_, v_h__2_353_);
lean_dec(v_fuel_351_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter___redArg(lean_object* v_p_u2081_355_, lean_object* v_p_u2082_356_, lean_object* v_h__1_357_, lean_object* v_h__2_358_, lean_object* v_h__3_359_, lean_object* v_h__4_360_){
_start:
{
if (lean_obj_tag(v_p_u2081_355_) == 0)
{
lean_dec(v_h__4_360_);
lean_dec(v_h__3_359_);
if (lean_obj_tag(v_p_u2082_356_) == 0)
{
lean_object* v_k_361_; lean_object* v_k_362_; lean_object* v___x_363_; 
lean_dec(v_h__2_358_);
v_k_361_ = lean_ctor_get(v_p_u2081_355_, 0);
lean_inc(v_k_361_);
lean_dec_ref_known(v_p_u2081_355_, 1);
v_k_362_ = lean_ctor_get(v_p_u2082_356_, 0);
lean_inc(v_k_362_);
lean_dec_ref_known(v_p_u2082_356_, 1);
v___x_363_ = lean_apply_2(v_h__1_357_, v_k_361_, v_k_362_);
return v___x_363_;
}
else
{
lean_object* v_k_364_; lean_object* v_k_365_; lean_object* v_v_366_; lean_object* v_p_367_; lean_object* v___x_368_; 
lean_dec(v_h__1_357_);
v_k_364_ = lean_ctor_get(v_p_u2081_355_, 0);
lean_inc(v_k_364_);
lean_dec_ref_known(v_p_u2081_355_, 1);
v_k_365_ = lean_ctor_get(v_p_u2082_356_, 0);
lean_inc(v_k_365_);
v_v_366_ = lean_ctor_get(v_p_u2082_356_, 1);
lean_inc(v_v_366_);
v_p_367_ = lean_ctor_get(v_p_u2082_356_, 2);
lean_inc_ref(v_p_367_);
lean_dec_ref_known(v_p_u2082_356_, 3);
v___x_368_ = lean_apply_4(v_h__2_358_, v_k_364_, v_k_365_, v_v_366_, v_p_367_);
return v___x_368_;
}
}
else
{
lean_dec(v_h__2_358_);
lean_dec(v_h__1_357_);
if (lean_obj_tag(v_p_u2082_356_) == 0)
{
lean_object* v_k_369_; lean_object* v_v_370_; lean_object* v_p_371_; lean_object* v_k_372_; lean_object* v___x_373_; 
lean_dec(v_h__4_360_);
v_k_369_ = lean_ctor_get(v_p_u2081_355_, 0);
lean_inc(v_k_369_);
v_v_370_ = lean_ctor_get(v_p_u2081_355_, 1);
lean_inc(v_v_370_);
v_p_371_ = lean_ctor_get(v_p_u2081_355_, 2);
lean_inc_ref(v_p_371_);
lean_dec_ref_known(v_p_u2081_355_, 3);
v_k_372_ = lean_ctor_get(v_p_u2082_356_, 0);
lean_inc(v_k_372_);
lean_dec_ref_known(v_p_u2082_356_, 1);
v___x_373_ = lean_apply_4(v_h__3_359_, v_k_369_, v_v_370_, v_p_371_, v_k_372_);
return v___x_373_;
}
else
{
lean_object* v_k_374_; lean_object* v_v_375_; lean_object* v_p_376_; lean_object* v_k_377_; lean_object* v_v_378_; lean_object* v_p_379_; lean_object* v___x_380_; 
lean_dec(v_h__3_359_);
v_k_374_ = lean_ctor_get(v_p_u2081_355_, 0);
lean_inc(v_k_374_);
v_v_375_ = lean_ctor_get(v_p_u2081_355_, 1);
lean_inc(v_v_375_);
v_p_376_ = lean_ctor_get(v_p_u2081_355_, 2);
lean_inc_ref(v_p_376_);
lean_dec_ref_known(v_p_u2081_355_, 3);
v_k_377_ = lean_ctor_get(v_p_u2082_356_, 0);
lean_inc(v_k_377_);
v_v_378_ = lean_ctor_get(v_p_u2082_356_, 1);
lean_inc(v_v_378_);
v_p_379_ = lean_ctor_get(v_p_u2082_356_, 2);
lean_inc_ref(v_p_379_);
lean_dec_ref_known(v_p_u2082_356_, 3);
v___x_380_ = lean_apply_6(v_h__4_360_, v_k_374_, v_v_375_, v_p_376_, v_k_377_, v_v_378_, v_p_379_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_combine_go_match__1_splitter(lean_object* v_motive_381_, lean_object* v_p_u2081_382_, lean_object* v_p_u2082_383_, lean_object* v_h__1_384_, lean_object* v_h__2_385_, lean_object* v_h__3_386_, lean_object* v_h__4_387_){
_start:
{
if (lean_obj_tag(v_p_u2081_382_) == 0)
{
lean_dec(v_h__4_387_);
lean_dec(v_h__3_386_);
if (lean_obj_tag(v_p_u2082_383_) == 0)
{
lean_object* v_k_388_; lean_object* v_k_389_; lean_object* v___x_390_; 
lean_dec(v_h__2_385_);
v_k_388_ = lean_ctor_get(v_p_u2081_382_, 0);
lean_inc(v_k_388_);
lean_dec_ref_known(v_p_u2081_382_, 1);
v_k_389_ = lean_ctor_get(v_p_u2082_383_, 0);
lean_inc(v_k_389_);
lean_dec_ref_known(v_p_u2082_383_, 1);
v___x_390_ = lean_apply_2(v_h__1_384_, v_k_388_, v_k_389_);
return v___x_390_;
}
else
{
lean_object* v_k_391_; lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_p_394_; lean_object* v___x_395_; 
lean_dec(v_h__1_384_);
v_k_391_ = lean_ctor_get(v_p_u2081_382_, 0);
lean_inc(v_k_391_);
lean_dec_ref_known(v_p_u2081_382_, 1);
v_k_392_ = lean_ctor_get(v_p_u2082_383_, 0);
lean_inc(v_k_392_);
v_v_393_ = lean_ctor_get(v_p_u2082_383_, 1);
lean_inc(v_v_393_);
v_p_394_ = lean_ctor_get(v_p_u2082_383_, 2);
lean_inc_ref(v_p_394_);
lean_dec_ref_known(v_p_u2082_383_, 3);
v___x_395_ = lean_apply_4(v_h__2_385_, v_k_391_, v_k_392_, v_v_393_, v_p_394_);
return v___x_395_;
}
}
else
{
lean_dec(v_h__2_385_);
lean_dec(v_h__1_384_);
if (lean_obj_tag(v_p_u2082_383_) == 0)
{
lean_object* v_k_396_; lean_object* v_v_397_; lean_object* v_p_398_; lean_object* v_k_399_; lean_object* v___x_400_; 
lean_dec(v_h__4_387_);
v_k_396_ = lean_ctor_get(v_p_u2081_382_, 0);
lean_inc(v_k_396_);
v_v_397_ = lean_ctor_get(v_p_u2081_382_, 1);
lean_inc(v_v_397_);
v_p_398_ = lean_ctor_get(v_p_u2081_382_, 2);
lean_inc_ref(v_p_398_);
lean_dec_ref_known(v_p_u2081_382_, 3);
v_k_399_ = lean_ctor_get(v_p_u2082_383_, 0);
lean_inc(v_k_399_);
lean_dec_ref_known(v_p_u2082_383_, 1);
v___x_400_ = lean_apply_4(v_h__3_386_, v_k_396_, v_v_397_, v_p_398_, v_k_399_);
return v___x_400_;
}
else
{
lean_object* v_k_401_; lean_object* v_v_402_; lean_object* v_p_403_; lean_object* v_k_404_; lean_object* v_v_405_; lean_object* v_p_406_; lean_object* v___x_407_; 
lean_dec(v_h__3_386_);
v_k_401_ = lean_ctor_get(v_p_u2081_382_, 0);
lean_inc(v_k_401_);
v_v_402_ = lean_ctor_get(v_p_u2081_382_, 1);
lean_inc(v_v_402_);
v_p_403_ = lean_ctor_get(v_p_u2081_382_, 2);
lean_inc_ref(v_p_403_);
lean_dec_ref_known(v_p_u2081_382_, 3);
v_k_404_ = lean_ctor_get(v_p_u2082_383_, 0);
lean_inc(v_k_404_);
v_v_405_ = lean_ctor_get(v_p_u2082_383_, 1);
lean_inc(v_v_405_);
v_p_406_ = lean_ctor_get(v_p_u2082_383_, 2);
lean_inc_ref(v_p_406_);
lean_dec_ref_known(v_p_u2082_383_, 3);
v___x_407_ = lean_apply_6(v_h__4_387_, v_k_401_, v_v_402_, v_p_403_, v_k_404_, v_v_405_, v_p_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(lean_object* v_k_408_, lean_object* v_h__1_409_, lean_object* v_h__2_410_, lean_object* v_h__3_411_){
_start:
{
lean_object* v_zero_412_; uint8_t v_isZero_413_; 
v_zero_412_ = lean_unsigned_to_nat(0u);
v_isZero_413_ = lean_nat_dec_eq(v_k_408_, v_zero_412_);
if (v_isZero_413_ == 1)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec(v_h__3_411_);
lean_dec(v_h__2_410_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_apply_1(v_h__1_409_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_one_416_; lean_object* v_n_417_; uint8_t v___x_418_; 
lean_dec(v_h__1_409_);
v_one_416_ = lean_unsigned_to_nat(1u);
v_n_417_ = lean_nat_sub(v_k_408_, v_one_416_);
v___x_418_ = lean_nat_dec_eq(v_n_417_, v_zero_412_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v_h__2_410_);
v___x_419_ = lean_apply_2(v_h__3_411_, v_n_417_, lean_box(0));
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v_n_417_);
lean_dec(v_h__3_411_);
v___x_420_ = lean_box(0);
v___x_421_ = lean_apply_1(v_h__2_410_, v___x_420_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg___boxed(lean_object* v_k_422_, lean_object* v_h__1_423_, lean_object* v_h__2_424_, lean_object* v_h__3_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___redArg(v_k_422_, v_h__1_423_, v_h__2_424_, v_h__3_425_);
lean_dec(v_k_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(lean_object* v_motive_427_, lean_object* v_k_428_, lean_object* v_h__1_429_, lean_object* v_h__2_430_, lean_object* v_h__3_431_){
_start:
{
lean_object* v_zero_432_; uint8_t v_isZero_433_; 
v_zero_432_ = lean_unsigned_to_nat(0u);
v_isZero_433_ = lean_nat_dec_eq(v_k_428_, v_zero_432_);
if (v_isZero_433_ == 1)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec(v_h__3_431_);
lean_dec(v_h__2_430_);
v___x_434_ = lean_box(0);
v___x_435_ = lean_apply_1(v_h__1_429_, v___x_434_);
return v___x_435_;
}
else
{
lean_object* v_one_436_; lean_object* v_n_437_; uint8_t v___x_438_; 
lean_dec(v_h__1_429_);
v_one_436_ = lean_unsigned_to_nat(1u);
v_n_437_ = lean_nat_sub(v_k_428_, v_one_436_);
v___x_438_ = lean_nat_dec_eq(v_n_437_, v_zero_432_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_h__2_430_);
v___x_439_ = lean_apply_2(v_h__3_431_, v_n_437_, lean_box(0));
return v___x_439_;
}
else
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_dec(v_n_437_);
lean_dec(v_h__3_431_);
v___x_440_ = lean_box(0);
v___x_441_ = lean_apply_1(v_h__2_430_, v___x_440_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter___boxed(lean_object* v_motive_442_, lean_object* v_k_443_, lean_object* v_h__1_444_, lean_object* v_h__2_445_, lean_object* v_h__3_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_pow_match__1_splitter(v_motive_442_, v_k_443_, v_h__1_444_, v_h__2_445_, v_h__3_446_);
lean_dec(v_k_443_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_448_, lean_object* v_h__1_449_, lean_object* v_h__2_450_, lean_object* v_h__3_451_, lean_object* v_h__4_452_, lean_object* v_h__5_453_, lean_object* v_h__6_454_, lean_object* v_h__7_455_, lean_object* v_h__8_456_, lean_object* v_h__9_457_){
_start:
{
switch(lean_obj_tag(v_x_448_))
{
case 0:
{
lean_object* v_k_458_; lean_object* v___x_459_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
v_k_458_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_k_458_);
lean_dec_ref_known(v_x_448_, 1);
v___x_459_ = lean_apply_1(v_h__1_449_, v_k_458_);
return v___x_459_;
}
case 1:
{
lean_object* v_k_460_; lean_object* v___x_461_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_k_460_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_k_460_);
lean_dec_ref_known(v_x_448_, 1);
v___x_461_ = lean_apply_1(v_h__6_454_, v_k_460_);
return v___x_461_;
}
case 2:
{
lean_object* v_k_462_; lean_object* v___x_463_; 
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_k_462_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_k_462_);
lean_dec_ref_known(v_x_448_, 1);
v___x_463_ = lean_apply_1(v_h__9_457_, v_k_462_);
return v___x_463_;
}
case 3:
{
lean_object* v_i_464_; lean_object* v___x_465_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__1_449_);
v_i_464_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_i_464_);
lean_dec_ref_known(v_x_448_, 1);
v___x_465_ = lean_apply_1(v_h__2_450_, v_i_464_);
return v___x_465_;
}
case 4:
{
lean_object* v_a_466_; lean_object* v___x_467_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_a_466_ = lean_ctor_get(v_x_448_, 0);
lean_inc_ref(v_a_466_);
lean_dec_ref_known(v_x_448_, 1);
v___x_467_ = lean_apply_1(v_h__8_456_, v_a_466_);
return v___x_467_;
}
case 5:
{
lean_object* v_a_468_; lean_object* v_b_469_; lean_object* v___x_470_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_a_468_ = lean_ctor_get(v_x_448_, 0);
lean_inc_ref(v_a_468_);
v_b_469_ = lean_ctor_get(v_x_448_, 1);
lean_inc_ref(v_b_469_);
lean_dec_ref_known(v_x_448_, 2);
v___x_470_ = lean_apply_2(v_h__3_451_, v_a_468_, v_b_469_);
return v___x_470_;
}
case 6:
{
lean_object* v_a_471_; lean_object* v_b_472_; lean_object* v___x_473_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_a_471_ = lean_ctor_get(v_x_448_, 0);
lean_inc_ref(v_a_471_);
v_b_472_ = lean_ctor_get(v_x_448_, 1);
lean_inc_ref(v_b_472_);
lean_dec_ref_known(v_x_448_, 2);
v___x_473_ = lean_apply_2(v_h__7_455_, v_a_471_, v_b_472_);
return v___x_473_;
}
case 7:
{
lean_object* v_a_474_; lean_object* v_b_475_; lean_object* v___x_476_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__5_453_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_a_474_ = lean_ctor_get(v_x_448_, 0);
lean_inc_ref(v_a_474_);
v_b_475_ = lean_ctor_get(v_x_448_, 1);
lean_inc_ref(v_b_475_);
lean_dec_ref_known(v_x_448_, 2);
v___x_476_ = lean_apply_2(v_h__4_452_, v_a_474_, v_b_475_);
return v___x_476_;
}
default: 
{
lean_object* v_a_477_; lean_object* v_k_478_; lean_object* v___x_479_; 
lean_dec(v_h__9_457_);
lean_dec(v_h__8_456_);
lean_dec(v_h__7_455_);
lean_dec(v_h__6_454_);
lean_dec(v_h__4_452_);
lean_dec(v_h__3_451_);
lean_dec(v_h__2_450_);
lean_dec(v_h__1_449_);
v_a_477_ = lean_ctor_get(v_x_448_, 0);
lean_inc_ref(v_a_477_);
v_k_478_ = lean_ctor_get(v_x_448_, 1);
lean_inc(v_k_478_);
lean_dec_ref_known(v_x_448_, 2);
v___x_479_ = lean_apply_2(v_h__5_453_, v_a_477_, v_k_478_);
return v___x_479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_480_, lean_object* v_x_481_, lean_object* v_h__1_482_, lean_object* v_h__2_483_, lean_object* v_h__3_484_, lean_object* v_h__4_485_, lean_object* v_h__5_486_, lean_object* v_h__6_487_, lean_object* v_h__7_488_, lean_object* v_h__8_489_, lean_object* v_h__9_490_){
_start:
{
switch(lean_obj_tag(v_x_481_))
{
case 0:
{
lean_object* v_k_491_; lean_object* v___x_492_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
v_k_491_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_k_491_);
lean_dec_ref_known(v_x_481_, 1);
v___x_492_ = lean_apply_1(v_h__1_482_, v_k_491_);
return v___x_492_;
}
case 1:
{
lean_object* v_k_493_; lean_object* v___x_494_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_k_493_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_k_493_);
lean_dec_ref_known(v_x_481_, 1);
v___x_494_ = lean_apply_1(v_h__6_487_, v_k_493_);
return v___x_494_;
}
case 2:
{
lean_object* v_k_495_; lean_object* v___x_496_; 
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_k_495_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_k_495_);
lean_dec_ref_known(v_x_481_, 1);
v___x_496_ = lean_apply_1(v_h__9_490_, v_k_495_);
return v___x_496_;
}
case 3:
{
lean_object* v_i_497_; lean_object* v___x_498_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__1_482_);
v_i_497_ = lean_ctor_get(v_x_481_, 0);
lean_inc(v_i_497_);
lean_dec_ref_known(v_x_481_, 1);
v___x_498_ = lean_apply_1(v_h__2_483_, v_i_497_);
return v___x_498_;
}
case 4:
{
lean_object* v_a_499_; lean_object* v___x_500_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_a_499_ = lean_ctor_get(v_x_481_, 0);
lean_inc_ref(v_a_499_);
lean_dec_ref_known(v_x_481_, 1);
v___x_500_ = lean_apply_1(v_h__8_489_, v_a_499_);
return v___x_500_;
}
case 5:
{
lean_object* v_a_501_; lean_object* v_b_502_; lean_object* v___x_503_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_a_501_ = lean_ctor_get(v_x_481_, 0);
lean_inc_ref(v_a_501_);
v_b_502_ = lean_ctor_get(v_x_481_, 1);
lean_inc_ref(v_b_502_);
lean_dec_ref_known(v_x_481_, 2);
v___x_503_ = lean_apply_2(v_h__3_484_, v_a_501_, v_b_502_);
return v___x_503_;
}
case 6:
{
lean_object* v_a_504_; lean_object* v_b_505_; lean_object* v___x_506_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_a_504_ = lean_ctor_get(v_x_481_, 0);
lean_inc_ref(v_a_504_);
v_b_505_ = lean_ctor_get(v_x_481_, 1);
lean_inc_ref(v_b_505_);
lean_dec_ref_known(v_x_481_, 2);
v___x_506_ = lean_apply_2(v_h__7_488_, v_a_504_, v_b_505_);
return v___x_506_;
}
case 7:
{
lean_object* v_a_507_; lean_object* v_b_508_; lean_object* v___x_509_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__5_486_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_a_507_ = lean_ctor_get(v_x_481_, 0);
lean_inc_ref(v_a_507_);
v_b_508_ = lean_ctor_get(v_x_481_, 1);
lean_inc_ref(v_b_508_);
lean_dec_ref_known(v_x_481_, 2);
v___x_509_ = lean_apply_2(v_h__4_485_, v_a_507_, v_b_508_);
return v___x_509_;
}
default: 
{
lean_object* v_a_510_; lean_object* v_k_511_; lean_object* v___x_512_; 
lean_dec(v_h__9_490_);
lean_dec(v_h__8_489_);
lean_dec(v_h__7_488_);
lean_dec(v_h__6_487_);
lean_dec(v_h__4_485_);
lean_dec(v_h__3_484_);
lean_dec(v_h__2_483_);
lean_dec(v_h__1_482_);
v_a_510_ = lean_ctor_get(v_x_481_, 0);
lean_inc_ref(v_a_510_);
v_k_511_ = lean_ctor_get(v_x_481_, 1);
lean_inc(v_k_511_);
lean_dec_ref_known(v_x_481_, 2);
v___x_512_ = lean_apply_2(v_h__5_486_, v_a_510_, v_k_511_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_513_, lean_object* v_h__1_514_, lean_object* v_h__2_515_, lean_object* v_h__3_516_){
_start:
{
switch(lean_obj_tag(v_a_513_))
{
case 0:
{
lean_object* v_k_517_; lean_object* v___x_518_; 
lean_dec(v_h__3_516_);
lean_dec(v_h__2_515_);
v_k_517_ = lean_ctor_get(v_a_513_, 0);
lean_inc(v_k_517_);
lean_dec_ref_known(v_a_513_, 1);
v___x_518_ = lean_apply_1(v_h__1_514_, v_k_517_);
return v___x_518_;
}
case 3:
{
lean_object* v_i_519_; lean_object* v___x_520_; 
lean_dec(v_h__3_516_);
lean_dec(v_h__1_514_);
v_i_519_ = lean_ctor_get(v_a_513_, 0);
lean_inc(v_i_519_);
lean_dec_ref_known(v_a_513_, 1);
v___x_520_ = lean_apply_1(v_h__2_515_, v_i_519_);
return v___x_520_;
}
default: 
{
lean_object* v___x_521_; 
lean_dec(v_h__2_515_);
lean_dec(v_h__1_514_);
v___x_521_ = lean_apply_3(v_h__3_516_, v_a_513_, lean_box(0), lean_box(0));
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_522_, lean_object* v_a_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_, lean_object* v_h__3_526_){
_start:
{
switch(lean_obj_tag(v_a_523_))
{
case 0:
{
lean_object* v_k_527_; lean_object* v___x_528_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__2_525_);
v_k_527_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_k_527_);
lean_dec_ref_known(v_a_523_, 1);
v___x_528_ = lean_apply_1(v_h__1_524_, v_k_527_);
return v___x_528_;
}
case 3:
{
lean_object* v_i_529_; lean_object* v___x_530_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__1_524_);
v_i_529_ = lean_ctor_get(v_a_523_, 0);
lean_inc(v_i_529_);
lean_dec_ref_known(v_a_523_, 1);
v___x_530_ = lean_apply_1(v_h__2_525_, v_i_529_);
return v___x_530_;
}
default: 
{
lean_object* v___x_531_; 
lean_dec(v_h__2_525_);
lean_dec(v_h__1_524_);
v___x_531_ = lean_apply_3(v_h__3_526_, v_a_523_, lean_box(0), lean_box(0));
return v___x_531_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__cert(lean_object* v_lhs_532_, lean_object* v_rhs_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_532_);
v___x_535_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_533_);
v___x_536_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_534_, v___x_535_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v___x_534_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__cert___boxed(lean_object* v_lhs_537_, lean_object* v_rhs_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_537_, v_rhs_538_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_CommRing_eq__normS__nc__cert(lean_object* v_lhs_541_, lean_object* v_rhs_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_543_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_541_);
v___x_544_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_542_);
v___x_545_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(lean_object* v_lhs_546_, lean_object* v_rhs_547_){
_start:
{
uint8_t v_res_548_; lean_object* v_r_549_; 
v_res_548_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_546_, v_rhs_547_);
v_r_549_ = lean_box(v_res_548_);
return v_r_549_;
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
