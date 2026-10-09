// Lean compiler output
// Module: Init.Grind.Module.NatModuleNorm
// Imports: public import Init.Grind.Ordered.Linarith import Init.Data.AC import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Omega
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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_combine(lean_object*, lean_object*);
lean_object* l_Lean_Grind_Linarith_Poly_mul(lean_object*, lean_object*);
uint8_t l_Lean_Grind_Linarith_instBEqPoly_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Expr_toPolyN___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg(lean_object* v_inst_1_, lean_object* v_ctx_2_, lean_object* v_x_3_){
_start:
{
switch(lean_obj_tag(v_x_3_))
{
case 1:
{
lean_object* v_i_4_; lean_object* v___x_5_; 
lean_dec_ref(v_inst_1_);
v_i_4_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_i_4_);
lean_dec_ref_known(v_x_3_, 1);
v___x_5_ = l_Lean_RArray_getImpl___redArg(v_ctx_2_, v_i_4_);
lean_dec(v_i_4_);
return v___x_5_;
}
case 2:
{
lean_object* v_toAddCommMonoid_6_; lean_object* v_toAdd_7_; lean_object* v_a_8_; lean_object* v_b_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v_toAddCommMonoid_6_ = lean_ctor_get(v_inst_1_, 0);
v_toAdd_7_ = lean_ctor_get(v_toAddCommMonoid_6_, 1);
lean_inc(v_toAdd_7_);
v_a_8_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_a_8_);
v_b_9_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_b_9_);
lean_dec_ref_known(v_x_3_, 2);
lean_inc_ref(v_inst_1_);
v___x_10_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_a_8_);
v___x_11_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_b_9_);
v___x_12_ = lean_apply_2(v_toAdd_7_, v___x_10_, v___x_11_);
return v___x_12_;
}
case 5:
{
lean_object* v_nsmul_13_; lean_object* v_k_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_nsmul_13_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_nsmul_13_);
v_k_14_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_k_14_);
v_a_15_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v_x_3_, 2);
v___x_16_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_a_15_);
v___x_17_ = lean_apply_2(v_nsmul_13_, v_k_14_, v___x_16_);
return v___x_17_;
}
default: 
{
lean_object* v_toAddCommMonoid_18_; lean_object* v_toZero_19_; 
v_toAddCommMonoid_18_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toAddCommMonoid_18_);
lean_dec(v_x_3_);
lean_dec_ref(v_inst_1_);
v_toZero_19_ = lean_ctor_get(v_toAddCommMonoid_18_, 0);
lean_inc(v_toZero_19_);
lean_dec_ref(v_toAddCommMonoid_18_);
return v_toZero_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(lean_object* v_inst_20_, lean_object* v_ctx_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_20_, v_ctx_21_, v_x_22_);
lean_dec_ref(v_ctx_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_ctx_26_, lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_25_, v_ctx_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___boxed(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_ctx_31_, lean_object* v_x_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Grind_Linarith_Expr_denoteN(v_00_u03b1_29_, v_inst_30_, v_ctx_31_, v_x_32_);
lean_dec_ref(v_ctx_31_);
return v_res_33_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg(lean_object* v_inst_36_, lean_object* v_ctx_37_, lean_object* v_p_38_){
_start:
{
if (lean_obj_tag(v_p_38_) == 0)
{
lean_object* v_toAddCommMonoid_39_; lean_object* v_toZero_40_; 
v_toAddCommMonoid_39_ = lean_ctor_get(v_inst_36_, 0);
lean_inc_ref(v_toAddCommMonoid_39_);
lean_dec_ref(v_inst_36_);
v_toZero_40_ = lean_ctor_get(v_toAddCommMonoid_39_, 0);
lean_inc(v_toZero_40_);
lean_dec_ref(v_toAddCommMonoid_39_);
return v_toZero_40_;
}
else
{
lean_object* v_toAddCommMonoid_41_; lean_object* v_nsmul_42_; lean_object* v_toZero_43_; lean_object* v_toAdd_44_; lean_object* v_k_45_; lean_object* v_v_46_; lean_object* v_p_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v_toAddCommMonoid_41_ = lean_ctor_get(v_inst_36_, 0);
v_nsmul_42_ = lean_ctor_get(v_inst_36_, 1);
v_toZero_43_ = lean_ctor_get(v_toAddCommMonoid_41_, 0);
v_toAdd_44_ = lean_ctor_get(v_toAddCommMonoid_41_, 1);
lean_inc(v_toAdd_44_);
v_k_45_ = lean_ctor_get(v_p_38_, 0);
v_v_46_ = lean_ctor_get(v_p_38_, 1);
v_p_47_ = lean_ctor_get(v_p_38_, 2);
v___x_48_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0, &l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0);
v___x_49_ = lean_int_dec_lt(v_k_45_, v___x_48_);
if (v___x_49_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_50_ = lean_nat_abs(v_k_45_);
v___x_51_ = l_Lean_RArray_getImpl___redArg(v_ctx_37_, v_v_46_);
lean_inc(v_nsmul_42_);
v___x_52_ = lean_apply_2(v_nsmul_42_, v___x_50_, v___x_51_);
v___x_53_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_36_, v_ctx_37_, v_p_47_);
v___x_54_ = lean_apply_2(v_toAdd_44_, v___x_52_, v___x_53_);
return v___x_54_;
}
else
{
lean_inc(v_toZero_43_);
lean_dec(v_toAdd_44_);
lean_dec_ref(v_inst_36_);
return v_toZero_43_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(lean_object* v_inst_55_, lean_object* v_ctx_56_, lean_object* v_p_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_55_, v_ctx_56_, v_p_57_);
lean_dec(v_p_57_);
lean_dec_ref(v_ctx_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_ctx_61_, lean_object* v_p_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_60_, v_ctx_61_, v_p_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___boxed(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_ctx_66_, lean_object* v_p_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Grind_Linarith_Poly_denoteN(v_00_u03b1_64_, v_inst_65_, v_ctx_66_, v_p_67_);
lean_dec(v_p_67_);
lean_dec_ref(v_ctx_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
if (lean_obj_tag(v_p_69_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_71_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__1_70_, v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_k_74_; lean_object* v_v_75_; lean_object* v_p_76_; lean_object* v___x_77_; 
lean_dec(v_h__1_70_);
v_k_74_ = lean_ctor_get(v_p_69_, 0);
lean_inc(v_k_74_);
v_v_75_ = lean_ctor_get(v_p_69_, 1);
lean_inc(v_v_75_);
v_p_76_ = lean_ctor_get(v_p_69_, 2);
lean_inc(v_p_76_);
lean_dec_ref_known(v_p_69_, 3);
v___x_77_ = lean_apply_3(v_h__2_71_, v_k_74_, v_v_75_, v_p_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_78_, lean_object* v_p_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
if (lean_obj_tag(v_p_79_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v_h__2_81_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_apply_1(v_h__1_80_, v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_k_84_; lean_object* v_v_85_; lean_object* v_p_86_; lean_object* v___x_87_; 
lean_dec(v_h__1_80_);
v_k_84_ = lean_ctor_get(v_p_79_, 0);
lean_inc(v_k_84_);
v_v_85_ = lean_ctor_get(v_p_79_, 1);
lean_inc(v_v_85_);
v_p_86_ = lean_ctor_get(v_p_79_, 2);
lean_inc(v_p_86_);
lean_dec_ref_known(v_p_79_, 3);
v___x_87_ = lean_apply_3(v_h__2_81_, v_k_84_, v_v_85_, v_p_86_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_88_, lean_object* v_p_u2082_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_, lean_object* v_h__3_92_){
_start:
{
if (lean_obj_tag(v_p_u2081_88_) == 0)
{
lean_object* v___x_93_; 
lean_dec(v_h__3_92_);
lean_dec(v_h__2_91_);
v___x_93_ = lean_apply_1(v_h__1_90_, v_p_u2082_89_);
return v___x_93_;
}
else
{
lean_dec(v_h__1_90_);
if (lean_obj_tag(v_p_u2082_89_) == 0)
{
lean_object* v___x_94_; 
lean_dec(v_h__3_92_);
v___x_94_ = lean_apply_2(v_h__2_91_, v_p_u2081_88_, lean_box(0));
return v___x_94_;
}
else
{
lean_object* v_k_95_; lean_object* v_v_96_; lean_object* v_p_97_; lean_object* v_k_98_; lean_object* v_v_99_; lean_object* v_p_100_; lean_object* v___x_101_; 
lean_dec(v_h__2_91_);
v_k_95_ = lean_ctor_get(v_p_u2081_88_, 0);
lean_inc(v_k_95_);
v_v_96_ = lean_ctor_get(v_p_u2081_88_, 1);
lean_inc(v_v_96_);
v_p_97_ = lean_ctor_get(v_p_u2081_88_, 2);
lean_inc(v_p_97_);
lean_dec_ref_known(v_p_u2081_88_, 3);
v_k_98_ = lean_ctor_get(v_p_u2082_89_, 0);
lean_inc(v_k_98_);
v_v_99_ = lean_ctor_get(v_p_u2082_89_, 1);
lean_inc(v_v_99_);
v_p_100_ = lean_ctor_get(v_p_u2082_89_, 2);
lean_inc(v_p_100_);
lean_dec_ref_known(v_p_u2082_89_, 3);
v___x_101_ = lean_apply_6(v_h__3_92_, v_k_95_, v_v_96_, v_p_97_, v_k_98_, v_v_99_, v_p_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_102_, lean_object* v_p_u2081_103_, lean_object* v_p_u2082_104_, lean_object* v_h__1_105_, lean_object* v_h__2_106_, lean_object* v_h__3_107_){
_start:
{
if (lean_obj_tag(v_p_u2081_103_) == 0)
{
lean_object* v___x_108_; 
lean_dec(v_h__3_107_);
lean_dec(v_h__2_106_);
v___x_108_ = lean_apply_1(v_h__1_105_, v_p_u2082_104_);
return v___x_108_;
}
else
{
lean_dec(v_h__1_105_);
if (lean_obj_tag(v_p_u2082_104_) == 0)
{
lean_object* v___x_109_; 
lean_dec(v_h__3_107_);
v___x_109_ = lean_apply_2(v_h__2_106_, v_p_u2081_103_, lean_box(0));
return v___x_109_;
}
else
{
lean_object* v_k_110_; lean_object* v_v_111_; lean_object* v_p_112_; lean_object* v_k_113_; lean_object* v_v_114_; lean_object* v_p_115_; lean_object* v___x_116_; 
lean_dec(v_h__2_106_);
v_k_110_ = lean_ctor_get(v_p_u2081_103_, 0);
lean_inc(v_k_110_);
v_v_111_ = lean_ctor_get(v_p_u2081_103_, 1);
lean_inc(v_v_111_);
v_p_112_ = lean_ctor_get(v_p_u2081_103_, 2);
lean_inc(v_p_112_);
lean_dec_ref_known(v_p_u2081_103_, 3);
v_k_113_ = lean_ctor_get(v_p_u2082_104_, 0);
lean_inc(v_k_113_);
v_v_114_ = lean_ctor_get(v_p_u2082_104_, 1);
lean_inc(v_v_114_);
v_p_115_ = lean_ctor_get(v_p_u2082_104_, 2);
lean_inc(v_p_115_);
lean_dec_ref_known(v_p_u2082_104_, 3);
v___x_116_ = lean_apply_6(v_h__3_107_, v_k_110_, v_v_111_, v_p_112_, v_k_113_, v_v_114_, v_p_115_);
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object* v_a_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_nat_to_int(v_a_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object* v_x_121_){
_start:
{
switch(lean_obj_tag(v_x_121_))
{
case 1:
{
lean_object* v_i_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_i_122_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_i_122_);
lean_dec_ref_known(v_x_121_, 1);
v___x_123_ = lean_obj_once(&l_Lean_Grind_Linarith_Expr_toPolyN___closed__0, &l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once, _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0);
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v_i_122_);
lean_ctor_set(v___x_125_, 2, v___x_124_);
return v___x_125_;
}
case 2:
{
lean_object* v_a_126_; lean_object* v_b_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_a_126_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_a_126_);
v_b_127_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_b_127_);
lean_dec_ref_known(v_x_121_, 2);
v___x_128_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_126_);
v___x_129_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_b_127_);
v___x_130_ = l_Lean_Grind_Linarith_Poly_combine(v___x_128_, v___x_129_);
return v___x_130_;
}
case 5:
{
lean_object* v_k_131_; lean_object* v_a_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_131_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_k_131_);
v_a_132_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_a_132_);
lean_dec_ref_known(v_x_121_, 2);
v___x_133_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_132_);
v___x_134_ = lean_nat_to_int(v_k_131_);
v___x_135_ = l_Lean_Grind_Linarith_Poly_mul(v___x_133_, v___x_134_);
lean_dec(v___x_134_);
return v___x_135_;
}
default: 
{
lean_object* v___x_136_; 
lean_dec(v_x_121_);
v___x_136_ = lean_box(0);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_, lean_object* v_h__3_140_, lean_object* v_h__4_141_, lean_object* v_h__5_142_, lean_object* v_h__6_143_, lean_object* v_h__7_144_){
_start:
{
switch(lean_obj_tag(v_x_137_))
{
case 0:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v___x_145_ = lean_box(0);
v___x_146_ = lean_apply_1(v_h__4_141_, v___x_145_);
return v___x_146_;
}
case 1:
{
lean_object* v_i_147_; lean_object* v___x_148_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v_i_147_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_i_147_);
lean_dec_ref_known(v_x_137_, 1);
v___x_148_ = lean_apply_1(v_h__5_142_, v_i_147_);
return v___x_148_;
}
case 2:
{
lean_object* v_a_149_; lean_object* v_b_150_; lean_object* v___x_151_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v_a_149_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_149_);
v_b_150_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_b_150_);
lean_dec_ref_known(v_x_137_, 2);
v___x_151_ = lean_apply_2(v_h__6_143_, v_a_149_, v_b_150_);
return v___x_151_;
}
case 3:
{
lean_object* v_a_152_; lean_object* v_b_153_; lean_object* v___x_154_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
v_a_152_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_152_);
v_b_153_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_b_153_);
lean_dec_ref_known(v_x_137_, 2);
v___x_154_ = lean_apply_2(v_h__1_138_, v_a_152_, v_b_153_);
return v___x_154_;
}
case 4:
{
lean_object* v_a_155_; lean_object* v___x_156_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__1_138_);
v_a_155_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v_x_137_, 1);
v___x_156_ = lean_apply_1(v_h__2_139_, v_a_155_);
return v___x_156_;
}
case 5:
{
lean_object* v_k_157_; lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__3_140_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v_k_157_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_k_157_);
v_a_158_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_a_158_);
lean_dec_ref_known(v_x_137_, 2);
v___x_159_ = lean_apply_2(v_h__7_144_, v_k_157_, v_a_158_);
return v___x_159_;
}
default: 
{
lean_object* v_k_160_; lean_object* v_a_161_; lean_object* v___x_162_; 
lean_dec(v_h__7_144_);
lean_dec(v_h__6_143_);
lean_dec(v_h__5_142_);
lean_dec(v_h__4_141_);
lean_dec(v_h__2_139_);
lean_dec(v_h__1_138_);
v_k_160_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_k_160_);
v_a_161_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_a_161_);
lean_dec_ref_known(v_x_137_, 2);
v___x_162_ = lean_apply_2(v_h__3_140_, v_k_160_, v_a_161_);
return v___x_162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object* v_motive_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_, lean_object* v_h__3_167_, lean_object* v_h__4_168_, lean_object* v_h__5_169_, lean_object* v_h__6_170_, lean_object* v_h__7_171_){
_start:
{
switch(lean_obj_tag(v_x_164_))
{
case 0:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__6_170_);
lean_dec(v_h__5_169_);
lean_dec(v_h__3_167_);
lean_dec(v_h__2_166_);
lean_dec(v_h__1_165_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_apply_1(v_h__4_168_, v___x_172_);
return v___x_173_;
}
case 1:
{
lean_object* v_i_174_; lean_object* v___x_175_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__6_170_);
lean_dec(v_h__4_168_);
lean_dec(v_h__3_167_);
lean_dec(v_h__2_166_);
lean_dec(v_h__1_165_);
v_i_174_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_i_174_);
lean_dec_ref_known(v_x_164_, 1);
v___x_175_ = lean_apply_1(v_h__5_169_, v_i_174_);
return v___x_175_;
}
case 2:
{
lean_object* v_a_176_; lean_object* v_b_177_; lean_object* v___x_178_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__5_169_);
lean_dec(v_h__4_168_);
lean_dec(v_h__3_167_);
lean_dec(v_h__2_166_);
lean_dec(v_h__1_165_);
v_a_176_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_a_176_);
v_b_177_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_b_177_);
lean_dec_ref_known(v_x_164_, 2);
v___x_178_ = lean_apply_2(v_h__6_170_, v_a_176_, v_b_177_);
return v___x_178_;
}
case 3:
{
lean_object* v_a_179_; lean_object* v_b_180_; lean_object* v___x_181_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__6_170_);
lean_dec(v_h__5_169_);
lean_dec(v_h__4_168_);
lean_dec(v_h__3_167_);
lean_dec(v_h__2_166_);
v_a_179_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_a_179_);
v_b_180_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_b_180_);
lean_dec_ref_known(v_x_164_, 2);
v___x_181_ = lean_apply_2(v_h__1_165_, v_a_179_, v_b_180_);
return v___x_181_;
}
case 4:
{
lean_object* v_a_182_; lean_object* v___x_183_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__6_170_);
lean_dec(v_h__5_169_);
lean_dec(v_h__4_168_);
lean_dec(v_h__3_167_);
lean_dec(v_h__1_165_);
v_a_182_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v_x_164_, 1);
v___x_183_ = lean_apply_1(v_h__2_166_, v_a_182_);
return v___x_183_;
}
case 5:
{
lean_object* v_k_184_; lean_object* v_a_185_; lean_object* v___x_186_; 
lean_dec(v_h__6_170_);
lean_dec(v_h__5_169_);
lean_dec(v_h__4_168_);
lean_dec(v_h__3_167_);
lean_dec(v_h__2_166_);
lean_dec(v_h__1_165_);
v_k_184_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_k_184_);
v_a_185_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_a_185_);
lean_dec_ref_known(v_x_164_, 2);
v___x_186_ = lean_apply_2(v_h__7_171_, v_k_184_, v_a_185_);
return v___x_186_;
}
default: 
{
lean_object* v_k_187_; lean_object* v_a_188_; lean_object* v___x_189_; 
lean_dec(v_h__7_171_);
lean_dec(v_h__6_170_);
lean_dec(v_h__5_169_);
lean_dec(v_h__4_168_);
lean_dec(v_h__2_166_);
lean_dec(v_h__1_165_);
v_k_187_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_k_187_);
v_a_188_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_a_188_);
lean_dec_ref_known(v_x_164_, 2);
v___x_189_ = lean_apply_2(v_h__3_167_, v_k_187_, v_a_188_);
return v___x_189_;
}
}
}
}
uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object* v_lhs_190_, lean_object* v_rhs_191_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_192_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_lhs_190_);
v___x_193_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_rhs_191_);
v___x_194_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_192_, v___x_193_);
lean_dec(v___x_193_);
lean_dec(v___x_192_);
return v___x_194_;
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_eq__normN__cert_0interp(lean_interpreter_value* stack)
{
lean_object* v_lhs_190_ = stack[0].m_obj;
lean_object* v_rhs_191_ = stack[1].m_obj;
uint8_t v_res_195_;
v_res_195_ = l_Lean_Grind_Linarith_eq__normN__cert(v_lhs_190_, v_rhs_191_);
stack->m_num = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object* v_lhs_196_, lean_object* v_rhs_197_){
_start:
{
uint8_t v_res_198_; lean_object* v_r_199_; 
v_res_198_ = l_Lean_Grind_Linarith_eq__normN__cert(v_lhs_196_, v_rhs_197_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* initialize_Init_Data_AC(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Module_NatModuleNorm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Module_NatModuleNorm(builtin);
}
#ifdef __cplusplus
}
#endif
