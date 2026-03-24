// Lean compiler output
// Module: Init.Data.List.MinMaxIdx
// Imports: public import Init.Data.List.MinMaxOn import Init.Data.List.Nat.TakeDrop import Init.ByCases import Init.Data.Bool import Init.Data.List.Sublist import Init.Data.Nat.Lemmas import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_get___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_maxIdxOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(lean_object* v_inst_1_, lean_object* v_f_2_, lean_object* v_x_3_, lean_object* v_i_4_, lean_object* v_j_5_, lean_object* v_xs_6_){
_start:
{
if (lean_obj_tag(v_xs_6_) == 0)
{
lean_dec(v_j_5_);
lean_dec(v_x_3_);
lean_dec(v_f_2_);
lean_dec_ref(v_inst_1_);
return v_i_4_;
}
else
{
lean_object* v_head_7_; lean_object* v_tail_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_head_7_ = lean_ctor_get(v_xs_6_, 0);
lean_inc(v_head_7_);
v_tail_8_ = lean_ctor_get(v_xs_6_, 1);
lean_inc(v_tail_8_);
lean_dec_ref(v_xs_6_);
lean_inc(v_f_2_);
lean_inc(v_x_3_);
v___x_9_ = lean_apply_1(v_f_2_, v_x_3_);
lean_inc(v_f_2_);
lean_inc(v_head_7_);
v___x_10_ = lean_apply_1(v_f_2_, v_head_7_);
lean_inc_ref(v_inst_1_);
v___x_11_ = lean_apply_2(v_inst_1_, v___x_9_, v___x_10_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_i_4_);
lean_dec(v_x_3_);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_add(v_j_5_, v___x_13_);
v_x_3_ = v_head_7_;
v_i_4_ = v_j_5_;
v_j_5_ = v___x_14_;
v_xs_6_ = v_tail_8_;
goto _start;
}
else
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_head_7_);
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = lean_nat_add(v_j_5_, v___x_16_);
lean_dec(v_j_5_);
v_j_5_ = v___x_17_;
v_xs_6_ = v_tail_8_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go(lean_object* v_00_u03b2_19_, lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_inst_22_, lean_object* v_f_23_, lean_object* v_x_24_, lean_object* v_i_25_, lean_object* v_j_26_, lean_object* v_xs_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_22_, v_f_23_, v_x_24_, v_i_25_, v_j_26_, v_xs_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn___redArg(lean_object* v_inst_29_, lean_object* v_f_30_, lean_object* v_xs_31_){
_start:
{
lean_object* v_head_32_; lean_object* v_tail_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_head_32_ = lean_ctor_get(v_xs_31_, 0);
lean_inc(v_head_32_);
v_tail_33_ = lean_ctor_get(v_xs_31_, 1);
lean_inc(v_tail_33_);
lean_dec(v_xs_31_);
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_29_, v_f_30_, v_head_32_, v___x_34_, v___x_35_, v_tail_33_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn(lean_object* v_00_u03b2_37_, lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_f_41_, lean_object* v_xs_42_, lean_object* v_h_43_){
_start:
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v_head_44_ = lean_ctor_get(v_xs_42_, 0);
lean_inc(v_head_44_);
v_tail_45_ = lean_ctor_get(v_xs_42_, 1);
lean_inc(v_tail_45_);
lean_dec(v_xs_42_);
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_40_, v_f_41_, v_head_44_, v___x_46_, v___x_47_, v_tail_45_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f___redArg(lean_object* v_inst_49_, lean_object* v_f_50_, lean_object* v_xs_51_){
_start:
{
if (lean_obj_tag(v_xs_51_) == 0)
{
lean_object* v___x_52_; 
lean_dec(v_f_50_);
lean_dec_ref(v_inst_49_);
v___x_52_ = lean_box(0);
return v___x_52_;
}
else
{
lean_object* v_head_53_; lean_object* v_tail_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_head_53_ = lean_ctor_get(v_xs_51_, 0);
lean_inc(v_head_53_);
v_tail_54_ = lean_ctor_get(v_xs_51_, 1);
lean_inc(v_tail_54_);
lean_dec_ref(v_xs_51_);
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = lean_unsigned_to_nat(1u);
v___x_57_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_49_, v_f_50_, v_head_53_, v___x_55_, v___x_56_, v_tail_54_);
v___x_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_List_minIdxOn_x3f(lean_object* v_00_u03b2_59_, lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_f_63_, lean_object* v_xs_64_){
_start:
{
if (lean_obj_tag(v_xs_64_) == 0)
{
lean_object* v___x_65_; 
lean_dec(v_f_63_);
lean_dec_ref(v_inst_62_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
else
{
lean_object* v_head_66_; lean_object* v_tail_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_head_66_ = lean_ctor_get(v_xs_64_, 0);
lean_inc(v_head_66_);
v_tail_67_ = lean_ctor_get(v_xs_64_, 1);
lean_inc(v_tail_67_);
lean_dec_ref(v_xs_64_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_62_, v_f_63_, v_head_66_, v___x_68_, v___x_69_, v_tail_67_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT uint8_t l_List_maxIdxOn___redArg___lam__0(lean_object* v_inst_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_apply_2(v_inst_72_, v_b_74_, v_a_73_);
v___x_76_ = lean_unbox(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg___lam__0___boxed(lean_object* v_inst_77_, lean_object* v_a_78_, lean_object* v_b_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_List_maxIdxOn___redArg___lam__0(v_inst_77_, v_a_78_, v_b_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg(lean_object* v_inst_82_, lean_object* v_f_83_, lean_object* v_xs_84_){
_start:
{
lean_object* v_head_85_; lean_object* v_tail_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_head_85_ = lean_ctor_get(v_xs_84_, 0);
lean_inc(v_head_85_);
v_tail_86_ = lean_ctor_get(v_xs_84_, 1);
lean_inc(v_tail_86_);
lean_dec(v_xs_84_);
v___f_87_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_87_, 0, v_inst_82_);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_unsigned_to_nat(1u);
v___x_90_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_87_, v_f_83_, v_head_85_, v___x_88_, v___x_89_, v_tail_86_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn(lean_object* v_00_u03b2_91_, lean_object* v_00_u03b1_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_f_95_, lean_object* v_xs_96_, lean_object* v_h_97_){
_start:
{
lean_object* v_head_98_; lean_object* v_tail_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_head_98_ = lean_ctor_get(v_xs_96_, 0);
lean_inc(v_head_98_);
v_tail_99_ = lean_ctor_get(v_xs_96_, 1);
lean_inc(v_tail_99_);
lean_dec(v_xs_96_);
v___f_100_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_100_, 0, v_inst_94_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_100_, v_f_95_, v_head_98_, v___x_101_, v___x_102_, v_tail_99_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f___redArg(lean_object* v_inst_104_, lean_object* v_f_105_, lean_object* v_xs_106_){
_start:
{
if (lean_obj_tag(v_xs_106_) == 0)
{
lean_object* v___x_107_; 
lean_dec(v_f_105_);
lean_dec_ref(v_inst_104_);
v___x_107_ = lean_box(0);
return v___x_107_;
}
else
{
lean_object* v_head_108_; lean_object* v_tail_109_; lean_object* v___f_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_head_108_ = lean_ctor_get(v_xs_106_, 0);
lean_inc(v_head_108_);
v_tail_109_ = lean_ctor_get(v_xs_106_, 1);
lean_inc(v_tail_109_);
lean_dec_ref(v_xs_106_);
v___f_110_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_110_, 0, v_inst_104_);
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_110_, v_f_105_, v_head_108_, v___x_111_, v___x_112_, v_tail_109_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f(lean_object* v_00_u03b2_115_, lean_object* v_00_u03b1_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_f_119_, lean_object* v_xs_120_){
_start:
{
if (lean_obj_tag(v_xs_120_) == 0)
{
lean_object* v___x_121_; 
lean_dec(v_f_119_);
lean_dec_ref(v_inst_118_);
v___x_121_ = lean_box(0);
return v___x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_head_122_ = lean_ctor_get(v_xs_120_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_xs_120_, 1);
lean_inc(v_tail_123_);
lean_dec_ref(v_xs_120_);
v___f_124_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_124_, 0, v_inst_118_);
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_124_, v_f_119_, v_head_122_, v___x_125_, v___x_126_, v_tail_123_);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter___redArg(lean_object* v_xs_129_, lean_object* v_h__1_130_, lean_object* v_h__2_131_){
_start:
{
if (lean_obj_tag(v_xs_129_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_131_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_130_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_head_134_; lean_object* v_tail_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_130_);
v_head_134_ = lean_ctor_get(v_xs_129_, 0);
lean_inc(v_head_134_);
v_tail_135_ = lean_ctor_get(v_xs_129_, 1);
lean_inc(v_tail_135_);
lean_dec_ref(v_xs_129_);
v___x_136_ = lean_apply_2(v_h__2_131_, v_head_134_, v_tail_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__1_splitter(lean_object* v_00_u03b1_137_, lean_object* v_motive_138_, lean_object* v_xs_139_, lean_object* v_h__1_140_, lean_object* v_h__2_141_){
_start:
{
if (lean_obj_tag(v_xs_139_) == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_h__2_141_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_apply_1(v_h__1_140_, v___x_142_);
return v___x_143_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_146_; 
lean_dec(v_h__1_140_);
v_head_144_ = lean_ctor_get(v_xs_139_, 0);
lean_inc(v_head_144_);
v_tail_145_ = lean_ctor_get(v_xs_139_, 1);
lean_inc(v_tail_145_);
lean_dec_ref(v_xs_139_);
v___x_146_ = lean_apply_2(v_h__2_141_, v_head_144_, v_tail_145_);
return v___x_146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter___redArg(lean_object* v_xs_147_, lean_object* v_h__1_148_){
_start:
{
lean_object* v_head_149_; lean_object* v_tail_150_; lean_object* v___x_151_; 
v_head_149_ = lean_ctor_get(v_xs_147_, 0);
lean_inc(v_head_149_);
v_tail_150_ = lean_ctor_get(v_xs_147_, 1);
lean_inc(v_tail_150_);
lean_dec(v_xs_147_);
v___x_151_ = lean_apply_3(v_h__1_148_, v_head_149_, v_tail_150_, lean_box(0));
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter(lean_object* v_00_u03b1_152_, lean_object* v_motive_153_, lean_object* v_xs_154_, lean_object* v_h_155_, lean_object* v_h__1_156_){
_start:
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_159_; 
v_head_157_ = lean_ctor_get(v_xs_154_, 0);
lean_inc(v_head_157_);
v_tail_158_ = lean_ctor_get(v_xs_154_, 1);
lean_inc(v_tail_158_);
lean_dec(v_xs_154_);
v___x_159_ = lean_apply_3(v_h__1_156_, v_head_157_, v_tail_158_, lean_box(0));
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(lean_object* v_inst_160_, lean_object* v_f_161_, lean_object* v_xs_162_, lean_object* v_ys_163_, lean_object* v_i_164_, lean_object* v_j_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
lean_inc(v_i_164_);
v___x_166_ = l_List_get___redArg(v_xs_162_, v_i_164_);
lean_inc(v_f_161_);
v___x_167_ = lean_apply_1(v_f_161_, v___x_166_);
lean_inc(v_j_165_);
v___x_168_ = l_List_get___redArg(v_ys_163_, v_j_165_);
v___x_169_ = lean_apply_1(v_f_161_, v___x_168_);
v___x_170_ = lean_apply_2(v_inst_160_, v___x_167_, v___x_169_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v_i_164_);
v___x_172_ = l_List_lengthTR___redArg(v_xs_162_);
v___x_173_ = lean_nat_add(v___x_172_, v_j_165_);
lean_dec(v_j_165_);
lean_dec(v___x_172_);
return v___x_173_;
}
else
{
lean_dec(v_j_165_);
return v_i_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(lean_object* v_inst_174_, lean_object* v_f_175_, lean_object* v_xs_176_, lean_object* v_ys_177_, lean_object* v_i_178_, lean_object* v_j_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(v_inst_174_, v_f_175_, v_xs_176_, v_ys_177_, v_i_178_, v_j_179_);
lean_dec(v_ys_177_);
lean_dec(v_xs_176_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(lean_object* v_00_u03b2_181_, lean_object* v_00_u03b1_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_f_185_, lean_object* v_xs_186_, lean_object* v_ys_187_, lean_object* v_i_188_, lean_object* v_j_189_, lean_object* v_hi_190_, lean_object* v_hj_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(v_inst_184_, v_f_185_, v_xs_186_, v_ys_187_, v_i_188_, v_j_189_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(lean_object* v_00_u03b2_193_, lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_f_197_, lean_object* v_xs_198_, lean_object* v_ys_199_, lean_object* v_i_200_, lean_object* v_j_201_, lean_object* v_hi_202_, lean_object* v_hj_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(v_00_u03b2_193_, v_00_u03b1_194_, v_inst_195_, v_inst_196_, v_f_197_, v_xs_198_, v_ys_199_, v_i_200_, v_j_201_, v_hi_202_, v_hj_203_);
lean_dec(v_ys_199_);
lean_dec(v_xs_198_);
return v_res_204_;
}
}
lean_object* runtime_initialize_Init_Data_List_MinMaxOn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_MinMaxIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_MinMaxIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_MinMaxOn(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_MinMaxIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMaxIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_MinMaxIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_MinMaxIdx(builtin);
}
#ifdef __cplusplus
}
#endif
