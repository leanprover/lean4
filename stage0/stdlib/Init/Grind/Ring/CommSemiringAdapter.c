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
lean_object* l_Lean_Grind_Ring_OfSemiring_natCast___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_toQ___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_add___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_mul___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_Ring_OfSemiring_npow___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofVar(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mul__nc(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_ofMon(lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_pow__nc(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(lean_object* v_x_222_, lean_object* v_h__1_223_, lean_object* v_h__2_224_, lean_object* v_h__3_225_, lean_object* v_h__4_226_, lean_object* v_h__5_227_, lean_object* v_h__6_228_, lean_object* v_h__7_229_, lean_object* v_h__8_230_, lean_object* v_h__9_231_){
_start:
{
switch(lean_obj_tag(v_x_222_))
{
case 0:
{
lean_object* v_k_232_; lean_object* v___x_233_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
v_k_232_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_k_232_);
lean_dec_ref_known(v_x_222_, 1);
v___x_233_ = lean_apply_1(v_h__1_223_, v_k_232_);
return v___x_233_;
}
case 1:
{
lean_object* v_k_234_; lean_object* v___x_235_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_k_234_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_k_234_);
lean_dec_ref_known(v_x_222_, 1);
v___x_235_ = lean_apply_1(v_h__6_228_, v_k_234_);
return v___x_235_;
}
case 2:
{
lean_object* v_k_236_; lean_object* v___x_237_; 
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_k_236_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_k_236_);
lean_dec_ref_known(v_x_222_, 1);
v___x_237_ = lean_apply_1(v_h__9_231_, v_k_236_);
return v___x_237_;
}
case 3:
{
lean_object* v_i_238_; lean_object* v___x_239_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__1_223_);
v_i_238_ = lean_ctor_get(v_x_222_, 0);
lean_inc(v_i_238_);
lean_dec_ref_known(v_x_222_, 1);
v___x_239_ = lean_apply_1(v_h__2_224_, v_i_238_);
return v___x_239_;
}
case 4:
{
lean_object* v_a_240_; lean_object* v___x_241_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_a_240_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_a_240_);
lean_dec_ref_known(v_x_222_, 1);
v___x_241_ = lean_apply_1(v_h__8_230_, v_a_240_);
return v___x_241_;
}
case 5:
{
lean_object* v_a_242_; lean_object* v_b_243_; lean_object* v___x_244_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_a_242_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_a_242_);
v_b_243_ = lean_ctor_get(v_x_222_, 1);
lean_inc_ref(v_b_243_);
lean_dec_ref_known(v_x_222_, 2);
v___x_244_ = lean_apply_2(v_h__3_225_, v_a_242_, v_b_243_);
return v___x_244_;
}
case 6:
{
lean_object* v_a_245_; lean_object* v_b_246_; lean_object* v___x_247_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_a_245_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_a_245_);
v_b_246_ = lean_ctor_get(v_x_222_, 1);
lean_inc_ref(v_b_246_);
lean_dec_ref_known(v_x_222_, 2);
v___x_247_ = lean_apply_2(v_h__7_229_, v_a_245_, v_b_246_);
return v___x_247_;
}
case 7:
{
lean_object* v_a_248_; lean_object* v_b_249_; lean_object* v___x_250_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__5_227_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_a_248_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_a_248_);
v_b_249_ = lean_ctor_get(v_x_222_, 1);
lean_inc_ref(v_b_249_);
lean_dec_ref_known(v_x_222_, 2);
v___x_250_ = lean_apply_2(v_h__4_226_, v_a_248_, v_b_249_);
return v___x_250_;
}
default: 
{
lean_object* v_a_251_; lean_object* v_k_252_; lean_object* v___x_253_; 
lean_dec(v_h__9_231_);
lean_dec(v_h__8_230_);
lean_dec(v_h__7_229_);
lean_dec(v_h__6_228_);
lean_dec(v_h__4_226_);
lean_dec(v_h__3_225_);
lean_dec(v_h__2_224_);
lean_dec(v_h__1_223_);
v_a_251_ = lean_ctor_get(v_x_222_, 0);
lean_inc_ref(v_a_251_);
v_k_252_ = lean_ctor_get(v_x_222_, 1);
lean_inc(v_k_252_);
lean_dec_ref_known(v_x_222_, 2);
v___x_253_ = lean_apply_2(v_h__5_227_, v_a_251_, v_k_252_);
return v___x_253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(lean_object* v_motive_254_, lean_object* v_x_255_, lean_object* v_h__1_256_, lean_object* v_h__2_257_, lean_object* v_h__3_258_, lean_object* v_h__4_259_, lean_object* v_h__5_260_, lean_object* v_h__6_261_, lean_object* v_h__7_262_, lean_object* v_h__8_263_, lean_object* v_h__9_264_){
_start:
{
switch(lean_obj_tag(v_x_255_))
{
case 0:
{
lean_object* v_k_265_; lean_object* v___x_266_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
v_k_265_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_k_265_);
lean_dec_ref_known(v_x_255_, 1);
v___x_266_ = lean_apply_1(v_h__1_256_, v_k_265_);
return v___x_266_;
}
case 1:
{
lean_object* v_k_267_; lean_object* v___x_268_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_k_267_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_k_267_);
lean_dec_ref_known(v_x_255_, 1);
v___x_268_ = lean_apply_1(v_h__6_261_, v_k_267_);
return v___x_268_;
}
case 2:
{
lean_object* v_k_269_; lean_object* v___x_270_; 
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_k_269_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_k_269_);
lean_dec_ref_known(v_x_255_, 1);
v___x_270_ = lean_apply_1(v_h__9_264_, v_k_269_);
return v___x_270_;
}
case 3:
{
lean_object* v_i_271_; lean_object* v___x_272_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__1_256_);
v_i_271_ = lean_ctor_get(v_x_255_, 0);
lean_inc(v_i_271_);
lean_dec_ref_known(v_x_255_, 1);
v___x_272_ = lean_apply_1(v_h__2_257_, v_i_271_);
return v___x_272_;
}
case 4:
{
lean_object* v_a_273_; lean_object* v___x_274_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_a_273_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_273_);
lean_dec_ref_known(v_x_255_, 1);
v___x_274_ = lean_apply_1(v_h__8_263_, v_a_273_);
return v___x_274_;
}
case 5:
{
lean_object* v_a_275_; lean_object* v_b_276_; lean_object* v___x_277_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_a_275_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_275_);
v_b_276_ = lean_ctor_get(v_x_255_, 1);
lean_inc_ref(v_b_276_);
lean_dec_ref_known(v_x_255_, 2);
v___x_277_ = lean_apply_2(v_h__3_258_, v_a_275_, v_b_276_);
return v___x_277_;
}
case 6:
{
lean_object* v_a_278_; lean_object* v_b_279_; lean_object* v___x_280_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_a_278_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_278_);
v_b_279_ = lean_ctor_get(v_x_255_, 1);
lean_inc_ref(v_b_279_);
lean_dec_ref_known(v_x_255_, 2);
v___x_280_ = lean_apply_2(v_h__7_262_, v_a_278_, v_b_279_);
return v___x_280_;
}
case 7:
{
lean_object* v_a_281_; lean_object* v_b_282_; lean_object* v___x_283_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__5_260_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_a_281_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_281_);
v_b_282_ = lean_ctor_get(v_x_255_, 1);
lean_inc_ref(v_b_282_);
lean_dec_ref_known(v_x_255_, 2);
v___x_283_ = lean_apply_2(v_h__4_259_, v_a_281_, v_b_282_);
return v___x_283_;
}
default: 
{
lean_object* v_a_284_; lean_object* v_k_285_; lean_object* v___x_286_; 
lean_dec(v_h__9_264_);
lean_dec(v_h__8_263_);
lean_dec(v_h__7_262_);
lean_dec(v_h__6_261_);
lean_dec(v_h__4_259_);
lean_dec(v_h__3_258_);
lean_dec(v_h__2_257_);
lean_dec(v_h__1_256_);
v_a_284_ = lean_ctor_get(v_x_255_, 0);
lean_inc_ref(v_a_284_);
v_k_285_ = lean_ctor_get(v_x_255_, 1);
lean_inc(v_k_285_);
lean_dec_ref_known(v_x_255_, 2);
v___x_286_ = lean_apply_2(v_h__5_260_, v_a_284_, v_k_285_);
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(lean_object* v_a_287_, lean_object* v_h__1_288_, lean_object* v_h__2_289_, lean_object* v_h__3_290_){
_start:
{
switch(lean_obj_tag(v_a_287_))
{
case 0:
{
lean_object* v_k_291_; lean_object* v___x_292_; 
lean_dec(v_h__3_290_);
lean_dec(v_h__2_289_);
v_k_291_ = lean_ctor_get(v_a_287_, 0);
lean_inc(v_k_291_);
lean_dec_ref_known(v_a_287_, 1);
v___x_292_ = lean_apply_1(v_h__1_288_, v_k_291_);
return v___x_292_;
}
case 3:
{
lean_object* v_i_293_; lean_object* v___x_294_; 
lean_dec(v_h__3_290_);
lean_dec(v_h__1_288_);
v_i_293_ = lean_ctor_get(v_a_287_, 0);
lean_inc(v_i_293_);
lean_dec_ref_known(v_a_287_, 1);
v___x_294_ = lean_apply_1(v_h__2_289_, v_i_293_);
return v___x_294_;
}
default: 
{
lean_object* v___x_295_; 
lean_dec(v_h__2_289_);
lean_dec(v_h__1_288_);
v___x_295_ = lean_apply_3(v_h__3_290_, v_a_287_, lean_box(0), lean_box(0));
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(lean_object* v_motive_296_, lean_object* v_a_297_, lean_object* v_h__1_298_, lean_object* v_h__2_299_, lean_object* v_h__3_300_){
_start:
{
switch(lean_obj_tag(v_a_297_))
{
case 0:
{
lean_object* v_k_301_; lean_object* v___x_302_; 
lean_dec(v_h__3_300_);
lean_dec(v_h__2_299_);
v_k_301_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_k_301_);
lean_dec_ref_known(v_a_297_, 1);
v___x_302_ = lean_apply_1(v_h__1_298_, v_k_301_);
return v___x_302_;
}
case 3:
{
lean_object* v_i_303_; lean_object* v___x_304_; 
lean_dec(v_h__3_300_);
lean_dec(v_h__1_298_);
v_i_303_ = lean_ctor_get(v_a_297_, 0);
lean_inc(v_i_303_);
lean_dec_ref_known(v_a_297_, 1);
v___x_304_ = lean_apply_1(v_h__2_299_, v_i_303_);
return v___x_304_;
}
default: 
{
lean_object* v___x_305_; 
lean_dec(v_h__2_299_);
lean_dec(v_h__1_298_);
v___x_305_ = lean_apply_3(v_h__3_300_, v_a_297_, lean_box(0), lean_box(0));
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg(lean_object* v_inst_306_, lean_object* v_k_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_obj_once(&l_Lean_Grind_CommRing_Expr_toPolyS___closed__2, &l_Lean_Grind_CommRing_Expr_toPolyS___closed__2_once, _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__2);
v___x_310_ = lean_int_dec_lt(v_k_307_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v_ofNat_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_ofNat_311_ = lean_ctor_get(v_inst_306_, 3);
lean_inc(v_ofNat_311_);
lean_dec_ref(v_inst_306_);
v___x_312_ = lean_nat_abs(v_k_307_);
v___x_313_ = lean_apply_1(v_ofNat_311_, v___x_312_);
return v___x_313_;
}
else
{
lean_object* v_ofNat_314_; lean_object* v___x_315_; 
v_ofNat_314_ = lean_ctor_get(v_inst_306_, 3);
lean_inc(v_ofNat_314_);
lean_dec_ref(v_inst_306_);
v___x_315_ = lean_apply_1(v_ofNat_314_, v___x_308_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(lean_object* v_inst_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_316_, v_k_317_);
lean_dec(v_k_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_k_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_320_, v_k_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_denoteSInt___boxed(lean_object* v_00_u03b1_323_, lean_object* v_inst_324_, lean_object* v_k_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_323_, v_inst_324_, v_k_325_);
lean_dec(v_k_325_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg(lean_object* v_inst_327_, lean_object* v_ctx_328_, lean_object* v_p_329_){
_start:
{
if (lean_obj_tag(v_p_329_) == 0)
{
lean_object* v_k_330_; lean_object* v___x_331_; 
v_k_330_ = lean_ctor_get(v_p_329_, 0);
lean_inc(v_k_330_);
lean_dec_ref_known(v_p_329_, 1);
v___x_331_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_327_, v_k_330_);
lean_dec(v_k_330_);
return v___x_331_;
}
else
{
lean_object* v_toAdd_332_; lean_object* v_toMul_333_; lean_object* v_k_334_; lean_object* v_v_335_; lean_object* v_p_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_toAdd_332_ = lean_ctor_get(v_inst_327_, 0);
lean_inc(v_toAdd_332_);
v_toMul_333_ = lean_ctor_get(v_inst_327_, 1);
v_k_334_ = lean_ctor_get(v_p_329_, 0);
lean_inc(v_k_334_);
v_v_335_ = lean_ctor_get(v_p_329_, 1);
lean_inc(v_v_335_);
v_p_336_ = lean_ctor_get(v_p_329_, 2);
lean_inc_ref(v_p_336_);
lean_dec_ref_known(v_p_329_, 3);
lean_inc_ref_n(v_inst_327_, 2);
v___x_337_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_327_, v_k_334_);
lean_dec(v_k_334_);
v___x_338_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_327_, v_ctx_328_, v_v_335_);
lean_inc(v_toMul_333_);
v___x_339_ = lean_apply_2(v_toMul_333_, v___x_337_, v___x_338_);
v___x_340_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_327_, v_ctx_328_, v_p_336_);
v___x_341_ = lean_apply_2(v_toAdd_332_, v___x_339_, v___x_340_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(lean_object* v_inst_342_, lean_object* v_ctx_343_, lean_object* v_p_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_342_, v_ctx_343_, v_p_344_);
lean_dec_ref(v_ctx_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS(lean_object* v_00_u03b1_346_, lean_object* v_inst_347_, lean_object* v_ctx_348_, lean_object* v_p_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_347_, v_ctx_348_, v_p_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_denoteS___boxed(lean_object* v_00_u03b1_351_, lean_object* v_inst_352_, lean_object* v_ctx_353_, lean_object* v_p_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_351_, v_inst_352_, v_ctx_353_, v_p_354_);
lean_dec_ref(v_ctx_353_);
return v_res_355_;
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
