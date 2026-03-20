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
case 0:
{
lean_object* v_toAddCommMonoid_4_; lean_object* v_toZero_5_; 
v_toAddCommMonoid_4_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toAddCommMonoid_4_);
lean_dec_ref(v_inst_1_);
v_toZero_5_ = lean_ctor_get(v_toAddCommMonoid_4_, 0);
lean_inc(v_toZero_5_);
lean_dec_ref(v_toAddCommMonoid_4_);
return v_toZero_5_;
}
case 1:
{
lean_object* v_i_6_; lean_object* v___x_7_; 
lean_dec_ref(v_inst_1_);
v_i_6_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_i_6_);
lean_dec_ref(v_x_3_);
v___x_7_ = l_Lean_RArray_getImpl___redArg(v_ctx_2_, v_i_6_);
lean_dec(v_i_6_);
return v___x_7_;
}
case 2:
{
lean_object* v_toAddCommMonoid_8_; lean_object* v_toAdd_9_; lean_object* v_a_10_; lean_object* v_b_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_toAddCommMonoid_8_ = lean_ctor_get(v_inst_1_, 0);
v_toAdd_9_ = lean_ctor_get(v_toAddCommMonoid_8_, 1);
lean_inc(v_toAdd_9_);
v_a_10_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_a_10_);
v_b_11_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_b_11_);
lean_dec_ref(v_x_3_);
lean_inc_ref(v_inst_1_);
v___x_12_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_a_10_);
v___x_13_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_b_11_);
v___x_14_ = lean_apply_2(v_toAdd_9_, v___x_12_, v___x_13_);
return v___x_14_;
}
case 5:
{
lean_object* v_nsmul_15_; lean_object* v_k_16_; lean_object* v_a_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_nsmul_15_ = lean_ctor_get(v_inst_1_, 1);
lean_inc(v_nsmul_15_);
v_k_16_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_k_16_);
v_a_17_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_a_17_);
lean_dec_ref(v_x_3_);
v___x_18_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_1_, v_ctx_2_, v_a_17_);
v___x_19_ = lean_apply_2(v_nsmul_15_, v_k_16_, v___x_18_);
return v___x_19_;
}
default: 
{
lean_object* v_toAddCommMonoid_20_; lean_object* v_toZero_21_; 
v_toAddCommMonoid_20_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toAddCommMonoid_20_);
lean_dec(v_x_3_);
lean_dec_ref(v_inst_1_);
v_toZero_21_ = lean_ctor_get(v_toAddCommMonoid_20_, 0);
lean_inc(v_toZero_21_);
lean_dec_ref(v_toAddCommMonoid_20_);
return v_toZero_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(lean_object* v_inst_22_, lean_object* v_ctx_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_22_, v_ctx_23_, v_x_24_);
lean_dec_ref(v_ctx_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_ctx_28_, lean_object* v_x_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_27_, v_ctx_28_, v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_denoteN___boxed(lean_object* v_00_u03b1_31_, lean_object* v_inst_32_, lean_object* v_ctx_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Grind_Linarith_Expr_denoteN(v_00_u03b1_31_, v_inst_32_, v_ctx_33_, v_x_34_);
lean_dec_ref(v_ctx_33_);
return v_res_35_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg(lean_object* v_inst_38_, lean_object* v_ctx_39_, lean_object* v_p_40_){
_start:
{
if (lean_obj_tag(v_p_40_) == 0)
{
lean_object* v_toAddCommMonoid_41_; lean_object* v_toZero_42_; 
v_toAddCommMonoid_41_ = lean_ctor_get(v_inst_38_, 0);
lean_inc_ref(v_toAddCommMonoid_41_);
lean_dec_ref(v_inst_38_);
v_toZero_42_ = lean_ctor_get(v_toAddCommMonoid_41_, 0);
lean_inc(v_toZero_42_);
lean_dec_ref(v_toAddCommMonoid_41_);
return v_toZero_42_;
}
else
{
lean_object* v_toAddCommMonoid_43_; lean_object* v_nsmul_44_; lean_object* v_toZero_45_; lean_object* v_toAdd_46_; lean_object* v_k_47_; lean_object* v_v_48_; lean_object* v_p_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v_toAddCommMonoid_43_ = lean_ctor_get(v_inst_38_, 0);
v_nsmul_44_ = lean_ctor_get(v_inst_38_, 1);
v_toZero_45_ = lean_ctor_get(v_toAddCommMonoid_43_, 0);
v_toAdd_46_ = lean_ctor_get(v_toAddCommMonoid_43_, 1);
lean_inc(v_toAdd_46_);
v_k_47_ = lean_ctor_get(v_p_40_, 0);
v_v_48_ = lean_ctor_get(v_p_40_, 1);
v_p_49_ = lean_ctor_get(v_p_40_, 2);
v___x_50_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0, &l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0);
v___x_51_ = lean_int_dec_lt(v_k_47_, v___x_50_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_52_ = lean_nat_abs(v_k_47_);
v___x_53_ = l_Lean_RArray_getImpl___redArg(v_ctx_39_, v_v_48_);
lean_inc(v_nsmul_44_);
v___x_54_ = lean_apply_2(v_nsmul_44_, v___x_52_, v___x_53_);
v___x_55_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_38_, v_ctx_39_, v_p_49_);
v___x_56_ = lean_apply_2(v_toAdd_46_, v___x_54_, v___x_55_);
return v___x_56_;
}
else
{
lean_inc(v_toZero_45_);
lean_dec(v_toAdd_46_);
lean_dec_ref(v_inst_38_);
return v_toZero_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(lean_object* v_inst_57_, lean_object* v_ctx_58_, lean_object* v_p_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_57_, v_ctx_58_, v_p_59_);
lean_dec(v_p_59_);
lean_dec_ref(v_ctx_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_ctx_63_, lean_object* v_p_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_62_, v_ctx_63_, v_p_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_denoteN___boxed(lean_object* v_00_u03b1_66_, lean_object* v_inst_67_, lean_object* v_ctx_68_, lean_object* v_p_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Grind_Linarith_Poly_denoteN(v_00_u03b1_66_, v_inst_67_, v_ctx_68_, v_p_69_);
lean_dec(v_p_69_);
lean_dec_ref(v_ctx_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(lean_object* v_p_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_){
_start:
{
if (lean_obj_tag(v_p_71_) == 0)
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__2_73_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__1_72_, v___x_74_);
return v___x_75_;
}
else
{
lean_object* v_k_76_; lean_object* v_v_77_; lean_object* v_p_78_; lean_object* v___x_79_; 
lean_dec(v_h__1_72_);
v_k_76_ = lean_ctor_get(v_p_71_, 0);
lean_inc(v_k_76_);
v_v_77_ = lean_ctor_get(v_p_71_, 1);
lean_inc(v_v_77_);
v_p_78_ = lean_ctor_get(v_p_71_, 2);
lean_inc(v_p_78_);
lean_dec_ref(v_p_71_);
v___x_79_ = lean_apply_3(v_h__2_73_, v_k_76_, v_v_77_, v_p_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(lean_object* v_motive_80_, lean_object* v_p_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(v_p_81_, v_h__1_82_, v_h__2_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(lean_object* v_p_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_p_85_) == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__2_87_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__1_86_, v___x_88_);
return v___x_89_;
}
else
{
lean_object* v_k_90_; lean_object* v_v_91_; lean_object* v_p_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_86_);
v_k_90_ = lean_ctor_get(v_p_85_, 0);
lean_inc(v_k_90_);
v_v_91_ = lean_ctor_get(v_p_85_, 1);
lean_inc(v_v_91_);
v_p_92_ = lean_ctor_get(v_p_85_, 2);
lean_inc(v_p_92_);
lean_dec_ref(v_p_85_);
v___x_93_ = lean_apply_3(v_h__2_87_, v_k_90_, v_v_91_, v_p_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(lean_object* v_motive_94_, lean_object* v_p_95_, lean_object* v_h__1_96_, lean_object* v_h__2_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(v_p_95_, v_h__1_96_, v_h__2_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_nat_to_int(v_a_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_to_int(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_toPolyN(lean_object* v_x_103_){
_start:
{
switch(lean_obj_tag(v_x_103_))
{
case 0:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
case 1:
{
lean_object* v_i_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_i_105_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_i_105_);
lean_dec_ref(v_x_103_);
v___x_106_ = lean_obj_once(&l_Lean_Grind_Linarith_Expr_toPolyN___closed__0, &l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once, _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0);
v___x_107_ = lean_box(0);
v___x_108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v_i_105_);
lean_ctor_set(v___x_108_, 2, v___x_107_);
return v___x_108_;
}
case 2:
{
lean_object* v_a_109_; lean_object* v_b_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_a_109_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_a_109_);
v_b_110_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_b_110_);
lean_dec_ref(v_x_103_);
v___x_111_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_109_);
v___x_112_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_b_110_);
v___x_113_ = l_Lean_Grind_Linarith_Poly_combine(v___x_111_, v___x_112_);
return v___x_113_;
}
case 5:
{
lean_object* v_k_114_; lean_object* v_a_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_k_114_ = lean_ctor_get(v_x_103_, 0);
lean_inc(v_k_114_);
v_a_115_ = lean_ctor_get(v_x_103_, 1);
lean_inc(v_a_115_);
lean_dec_ref(v_x_103_);
v___x_116_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_115_);
v___x_117_ = lean_nat_to_int(v_k_114_);
v___x_118_ = l_Lean_Grind_Linarith_Poly_mul(v___x_116_, v___x_117_);
lean_dec(v___x_117_);
return v___x_118_;
}
default: 
{
lean_object* v___x_119_; 
lean_dec(v_x_103_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_, lean_object* v_h__3_123_, lean_object* v_h__4_124_, lean_object* v_h__5_125_, lean_object* v_h__6_126_, lean_object* v_h__7_127_){
_start:
{
switch(lean_obj_tag(v_x_120_))
{
case 0:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__6_126_);
lean_dec(v_h__5_125_);
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__4_124_, v___x_128_);
return v___x_129_;
}
case 1:
{
lean_object* v_i_130_; lean_object* v___x_131_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__6_126_);
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v_i_130_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_i_130_);
lean_dec_ref(v_x_120_);
v___x_131_ = lean_apply_1(v_h__5_125_, v_i_130_);
return v___x_131_;
}
case 2:
{
lean_object* v_a_132_; lean_object* v_b_133_; lean_object* v___x_134_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__5_125_);
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v_a_132_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_132_);
v_b_133_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_b_133_);
lean_dec_ref(v_x_120_);
v___x_134_ = lean_apply_2(v_h__6_126_, v_a_132_, v_b_133_);
return v___x_134_;
}
case 3:
{
lean_object* v_a_135_; lean_object* v_b_136_; lean_object* v___x_137_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__6_126_);
lean_dec(v_h__5_125_);
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
v_a_135_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_135_);
v_b_136_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_b_136_);
lean_dec_ref(v_x_120_);
v___x_137_ = lean_apply_2(v_h__1_121_, v_a_135_, v_b_136_);
return v___x_137_;
}
case 4:
{
lean_object* v_a_138_; lean_object* v___x_139_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__6_126_);
lean_dec(v_h__5_125_);
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
lean_dec(v_h__1_121_);
v_a_138_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v_x_120_);
v___x_139_ = lean_apply_1(v_h__2_122_, v_a_138_);
return v___x_139_;
}
case 5:
{
lean_object* v_k_140_; lean_object* v_a_141_; lean_object* v___x_142_; 
lean_dec(v_h__6_126_);
lean_dec(v_h__5_125_);
lean_dec(v_h__4_124_);
lean_dec(v_h__3_123_);
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v_k_140_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_k_140_);
v_a_141_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_a_141_);
lean_dec_ref(v_x_120_);
v___x_142_ = lean_apply_2(v_h__7_127_, v_k_140_, v_a_141_);
return v___x_142_;
}
default: 
{
lean_object* v_k_143_; lean_object* v_a_144_; lean_object* v___x_145_; 
lean_dec(v_h__7_127_);
lean_dec(v_h__6_126_);
lean_dec(v_h__5_125_);
lean_dec(v_h__4_124_);
lean_dec(v_h__2_122_);
lean_dec(v_h__1_121_);
v_k_143_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_k_143_);
v_a_144_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_a_144_);
lean_dec_ref(v_x_120_);
v___x_145_ = lean_apply_2(v_h__3_123_, v_k_143_, v_a_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(lean_object* v_motive_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_, lean_object* v_h__4_151_, lean_object* v_h__5_152_, lean_object* v_h__6_153_, lean_object* v_h__7_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(v_x_147_, v_h__1_148_, v_h__2_149_, v_h__3_150_, v_h__4_151_, v_h__5_152_, v_h__6_153_, v_h__7_154_);
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_Linarith_eq__normN__cert(lean_object* v_lhs_156_, lean_object* v_rhs_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_lhs_156_);
v___x_159_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_rhs_157_);
v___x_160_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_158_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v___x_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_eq__normN__cert___boxed(lean_object* v_lhs_161_, lean_object* v_rhs_162_){
_start:
{
uint8_t v_res_163_; lean_object* v_r_164_; 
v_res_163_ = l_Lean_Grind_Linarith_eq__normN__cert(v_lhs_161_, v_rhs_162_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_AC(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Module_NatModuleNorm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
