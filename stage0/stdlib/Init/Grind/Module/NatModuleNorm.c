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
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(lean_object* v_p_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(lean_object* v_motive_78_, lean_object* v_p_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
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
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_88_, lean_object* v_h__1_89_, lean_object* v_h__2_90_){
_start:
{
if (lean_obj_tag(v_p_88_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_90_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_89_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_k_93_; lean_object* v_v_94_; lean_object* v_p_95_; lean_object* v___x_96_; 
lean_dec(v_h__1_89_);
v_k_93_ = lean_ctor_get(v_p_88_, 0);
lean_inc(v_k_93_);
v_v_94_ = lean_ctor_get(v_p_88_, 1);
lean_inc(v_v_94_);
v_p_95_ = lean_ctor_get(v_p_88_, 2);
lean_inc(v_p_95_);
lean_dec_ref_known(v_p_88_, 3);
v___x_96_ = lean_apply_3(v_h__2_90_, v_k_93_, v_v_94_, v_p_95_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_97_, lean_object* v_p_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_p_98_) == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec(v_h__2_100_);
v___x_101_ = lean_box(0);
v___x_102_ = lean_apply_1(v_h__1_99_, v___x_101_);
return v___x_102_;
}
else
{
lean_object* v_k_103_; lean_object* v_v_104_; lean_object* v_p_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_99_);
v_k_103_ = lean_ctor_get(v_p_98_, 0);
lean_inc(v_k_103_);
v_v_104_ = lean_ctor_get(v_p_98_, 1);
lean_inc(v_v_104_);
v_p_105_ = lean_ctor_get(v_p_98_, 2);
lean_inc(v_p_105_);
lean_dec_ref_known(v_p_98_, 3);
v___x_106_ = lean_apply_3(v_h__2_100_, v_k_103_, v_v_104_, v_p_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter___redArg(lean_object* v_p_u2081_107_, lean_object* v_p_u2082_108_, lean_object* v_h__1_109_, lean_object* v_h__2_110_, lean_object* v_h__3_111_){
_start:
{
if (lean_obj_tag(v_p_u2081_107_) == 0)
{
lean_object* v___x_112_; 
lean_dec(v_h__3_111_);
lean_dec(v_h__2_110_);
v___x_112_ = lean_apply_1(v_h__1_109_, v_p_u2082_108_);
return v___x_112_;
}
else
{
lean_dec(v_h__1_109_);
if (lean_obj_tag(v_p_u2082_108_) == 0)
{
lean_object* v___x_113_; 
lean_dec(v_h__3_111_);
v___x_113_ = lean_apply_2(v_h__2_110_, v_p_u2081_107_, lean_box(0));
return v___x_113_;
}
else
{
lean_object* v_k_114_; lean_object* v_v_115_; lean_object* v_p_116_; lean_object* v_k_117_; lean_object* v_v_118_; lean_object* v_p_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_110_);
v_k_114_ = lean_ctor_get(v_p_u2081_107_, 0);
lean_inc(v_k_114_);
v_v_115_ = lean_ctor_get(v_p_u2081_107_, 1);
lean_inc(v_v_115_);
v_p_116_ = lean_ctor_get(v_p_u2081_107_, 2);
lean_inc(v_p_116_);
lean_dec_ref_known(v_p_u2081_107_, 3);
v_k_117_ = lean_ctor_get(v_p_u2082_108_, 0);
lean_inc(v_k_117_);
v_v_118_ = lean_ctor_get(v_p_u2082_108_, 1);
lean_inc(v_v_118_);
v_p_119_ = lean_ctor_get(v_p_u2082_108_, 2);
lean_inc(v_p_119_);
lean_dec_ref_known(v_p_u2082_108_, 3);
v___x_120_ = lean_apply_6(v_h__3_111_, v_k_114_, v_v_115_, v_p_116_, v_k_117_, v_v_118_, v_p_119_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_combine_match__1_splitter(lean_object* v_motive_121_, lean_object* v_p_u2081_122_, lean_object* v_p_u2082_123_, lean_object* v_h__1_124_, lean_object* v_h__2_125_, lean_object* v_h__3_126_){
_start:
{
if (lean_obj_tag(v_p_u2081_122_) == 0)
{
lean_object* v___x_127_; 
lean_dec(v_h__3_126_);
lean_dec(v_h__2_125_);
v___x_127_ = lean_apply_1(v_h__1_124_, v_p_u2082_123_);
return v___x_127_;
}
else
{
lean_dec(v_h__1_124_);
if (lean_obj_tag(v_p_u2082_123_) == 0)
{
lean_object* v___x_128_; 
lean_dec(v_h__3_126_);
v___x_128_ = lean_apply_2(v_h__2_125_, v_p_u2081_122_, lean_box(0));
return v___x_128_;
}
else
{
lean_object* v_k_129_; lean_object* v_v_130_; lean_object* v_p_131_; lean_object* v_k_132_; lean_object* v_v_133_; lean_object* v_p_134_; lean_object* v___x_135_; 
lean_dec(v_h__2_125_);
v_k_129_ = lean_ctor_get(v_p_u2081_122_, 0);
lean_inc(v_k_129_);
v_v_130_ = lean_ctor_get(v_p_u2081_122_, 1);
lean_inc(v_v_130_);
v_p_131_ = lean_ctor_get(v_p_u2081_122_, 2);
lean_inc(v_p_131_);
lean_dec_ref_known(v_p_u2081_122_, 3);
v_k_132_ = lean_ctor_get(v_p_u2082_123_, 0);
lean_inc(v_k_132_);
v_v_133_ = lean_ctor_get(v_p_u2082_123_, 1);
lean_inc(v_v_133_);
v_p_134_ = lean_ctor_get(v_p_u2082_123_, 2);
lean_inc(v_p_134_);
lean_dec_ref_known(v_p_u2082_123_, 3);
v___x_135_ = lean_apply_6(v_h__3_126_, v_k_129_, v_v_130_, v_p_131_, v_k_132_, v_v_133_, v_p_134_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_nat_to_int(v_a_136_);
return v___x_137_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1u);
v___x_139_ = lean_nat_to_int(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object* v_x_140_){
_start:
{
switch(lean_obj_tag(v_x_140_))
{
case 1:
{
lean_object* v_i_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_i_141_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_i_141_);
lean_dec_ref_known(v_x_140_, 1);
v___x_142_ = lean_obj_once(&l_Lean_Grind_Linarith_Expr_toPolyN___closed__0, &l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once, _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0);
v___x_143_ = lean_box(0);
v___x_144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v_i_141_);
lean_ctor_set(v___x_144_, 2, v___x_143_);
return v___x_144_;
}
case 2:
{
lean_object* v_a_145_; lean_object* v_b_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_a_145_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_a_145_);
v_b_146_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_b_146_);
lean_dec_ref_known(v_x_140_, 2);
v___x_147_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_145_);
v___x_148_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_b_146_);
v___x_149_ = l_Lean_Grind_Linarith_Poly_combine(v___x_147_, v___x_148_);
return v___x_149_;
}
case 5:
{
lean_object* v_k_150_; lean_object* v_a_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_k_150_ = lean_ctor_get(v_x_140_, 0);
lean_inc(v_k_150_);
v_a_151_ = lean_ctor_get(v_x_140_, 1);
lean_inc(v_a_151_);
lean_dec_ref_known(v_x_140_, 2);
v___x_152_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_151_);
v___x_153_ = lean_nat_to_int(v_k_150_);
v___x_154_ = l_Lean_Grind_Linarith_Poly_mul(v___x_152_, v___x_153_);
lean_dec(v___x_153_);
return v___x_154_;
}
default: 
{
lean_object* v___x_155_; 
lean_dec(v_x_140_);
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object* v_x_156_, lean_object* v_h__1_157_, lean_object* v_h__2_158_, lean_object* v_h__3_159_, lean_object* v_h__4_160_, lean_object* v_h__5_161_, lean_object* v_h__6_162_, lean_object* v_h__7_163_){
_start:
{
switch(lean_obj_tag(v_x_156_))
{
case 0:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__6_162_);
lean_dec(v_h__5_161_);
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v___x_164_ = lean_box(0);
v___x_165_ = lean_apply_1(v_h__4_160_, v___x_164_);
return v___x_165_;
}
case 1:
{
lean_object* v_i_166_; lean_object* v___x_167_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__6_162_);
lean_dec(v_h__4_160_);
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v_i_166_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_i_166_);
lean_dec_ref_known(v_x_156_, 1);
v___x_167_ = lean_apply_1(v_h__5_161_, v_i_166_);
return v___x_167_;
}
case 2:
{
lean_object* v_a_168_; lean_object* v_b_169_; lean_object* v___x_170_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__5_161_);
lean_dec(v_h__4_160_);
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v_a_168_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_a_168_);
v_b_169_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_b_169_);
lean_dec_ref_known(v_x_156_, 2);
v___x_170_ = lean_apply_2(v_h__6_162_, v_a_168_, v_b_169_);
return v___x_170_;
}
case 3:
{
lean_object* v_a_171_; lean_object* v_b_172_; lean_object* v___x_173_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__6_162_);
lean_dec(v_h__5_161_);
lean_dec(v_h__4_160_);
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
v_a_171_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_a_171_);
v_b_172_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_b_172_);
lean_dec_ref_known(v_x_156_, 2);
v___x_173_ = lean_apply_2(v_h__1_157_, v_a_171_, v_b_172_);
return v___x_173_;
}
case 4:
{
lean_object* v_a_174_; lean_object* v___x_175_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__6_162_);
lean_dec(v_h__5_161_);
lean_dec(v_h__4_160_);
lean_dec(v_h__3_159_);
lean_dec(v_h__1_157_);
v_a_174_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_a_174_);
lean_dec_ref_known(v_x_156_, 1);
v___x_175_ = lean_apply_1(v_h__2_158_, v_a_174_);
return v___x_175_;
}
case 5:
{
lean_object* v_k_176_; lean_object* v_a_177_; lean_object* v___x_178_; 
lean_dec(v_h__6_162_);
lean_dec(v_h__5_161_);
lean_dec(v_h__4_160_);
lean_dec(v_h__3_159_);
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v_k_176_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_k_176_);
v_a_177_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_a_177_);
lean_dec_ref_known(v_x_156_, 2);
v___x_178_ = lean_apply_2(v_h__7_163_, v_k_176_, v_a_177_);
return v___x_178_;
}
default: 
{
lean_object* v_k_179_; lean_object* v_a_180_; lean_object* v___x_181_; 
lean_dec(v_h__7_163_);
lean_dec(v_h__6_162_);
lean_dec(v_h__5_161_);
lean_dec(v_h__4_160_);
lean_dec(v_h__2_158_);
lean_dec(v_h__1_157_);
v_k_179_ = lean_ctor_get(v_x_156_, 0);
lean_inc(v_k_179_);
v_a_180_ = lean_ctor_get(v_x_156_, 1);
lean_inc(v_a_180_);
lean_dec_ref_known(v_x_156_, 2);
v___x_181_ = lean_apply_2(v_h__3_159_, v_k_179_, v_a_180_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object* v_motive_182_, lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_, lean_object* v_h__3_186_, lean_object* v_h__4_187_, lean_object* v_h__5_188_, lean_object* v_h__6_189_, lean_object* v_h__7_190_){
_start:
{
switch(lean_obj_tag(v_x_183_))
{
case 0:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__6_189_);
lean_dec(v_h__5_188_);
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_apply_1(v_h__4_187_, v___x_191_);
return v___x_192_;
}
case 1:
{
lean_object* v_i_193_; lean_object* v___x_194_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__6_189_);
lean_dec(v_h__4_187_);
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v_i_193_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_i_193_);
lean_dec_ref_known(v_x_183_, 1);
v___x_194_ = lean_apply_1(v_h__5_188_, v_i_193_);
return v___x_194_;
}
case 2:
{
lean_object* v_a_195_; lean_object* v_b_196_; lean_object* v___x_197_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__5_188_);
lean_dec(v_h__4_187_);
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v_a_195_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_a_195_);
v_b_196_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_b_196_);
lean_dec_ref_known(v_x_183_, 2);
v___x_197_ = lean_apply_2(v_h__6_189_, v_a_195_, v_b_196_);
return v___x_197_;
}
case 3:
{
lean_object* v_a_198_; lean_object* v_b_199_; lean_object* v___x_200_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__6_189_);
lean_dec(v_h__5_188_);
lean_dec(v_h__4_187_);
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
v_a_198_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_a_198_);
v_b_199_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_b_199_);
lean_dec_ref_known(v_x_183_, 2);
v___x_200_ = lean_apply_2(v_h__1_184_, v_a_198_, v_b_199_);
return v___x_200_;
}
case 4:
{
lean_object* v_a_201_; lean_object* v___x_202_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__6_189_);
lean_dec(v_h__5_188_);
lean_dec(v_h__4_187_);
lean_dec(v_h__3_186_);
lean_dec(v_h__1_184_);
v_a_201_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v_x_183_, 1);
v___x_202_ = lean_apply_1(v_h__2_185_, v_a_201_);
return v___x_202_;
}
case 5:
{
lean_object* v_k_203_; lean_object* v_a_204_; lean_object* v___x_205_; 
lean_dec(v_h__6_189_);
lean_dec(v_h__5_188_);
lean_dec(v_h__4_187_);
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v_k_203_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_k_203_);
v_a_204_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_a_204_);
lean_dec_ref_known(v_x_183_, 2);
v___x_205_ = lean_apply_2(v_h__7_190_, v_k_203_, v_a_204_);
return v___x_205_;
}
default: 
{
lean_object* v_k_206_; lean_object* v_a_207_; lean_object* v___x_208_; 
lean_dec(v_h__7_190_);
lean_dec(v_h__6_189_);
lean_dec(v_h__5_188_);
lean_dec(v_h__4_187_);
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v_k_206_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_k_206_);
v_a_207_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_a_207_);
lean_dec_ref_known(v_x_183_, 2);
v___x_208_ = lean_apply_2(v_h__3_186_, v_k_206_, v_a_207_);
return v___x_208_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object* v_lhs_209_, lean_object* v_rhs_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_211_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_lhs_209_);
v___x_212_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_rhs_210_);
v___x_213_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_211_, v___x_212_);
lean_dec(v___x_212_);
lean_dec(v___x_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object* v_lhs_214_, lean_object* v_rhs_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Lean_Grind_Linarith_eq__normN__cert(v_lhs_214_, v_rhs_215_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
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
