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
lean_inc_n(v_head_7_, 2);
v_tail_8_ = lean_ctor_get(v_xs_6_, 1);
lean_inc(v_tail_8_);
lean_dec_ref_known(v_xs_6_, 2);
lean_inc_n(v_f_2_, 2);
lean_inc(v_x_3_);
v___x_9_ = lean_apply_1(v_f_2_, v_x_3_);
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
lean_dec_ref_known(v_xs_51_, 2);
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
lean_dec_ref_known(v_xs_64_, 2);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_unsigned_to_nat(1u);
v___x_70_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v_inst_62_, v_f_63_, v_head_66_, v___x_68_, v___x_69_, v_tail_67_);
v___x_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
}
}
uint8_t l_List_maxIdxOn___redArg___lam__0(lean_object* v_inst_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_apply_2(v_inst_72_, v_b_74_, v_a_73_);
v___x_76_ = lean_unbox(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT void l_List_maxIdxOn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_72_ = stack[0].m_obj;
lean_object* v_a_73_ = stack[1].m_obj;
lean_object* v_b_74_ = stack[2].m_obj;
uint8_t v_res_77_;
v_res_77_ = l_List_maxIdxOn___redArg___lam__0(v_inst_72_, v_a_73_, v_b_74_);
stack->m_num = v_res_77_;
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg___lam__0___boxed(lean_object* v_inst_78_, lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_List_maxIdxOn___redArg___lam__0(v_inst_78_, v_a_79_, v_b_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn___redArg(lean_object* v_inst_83_, lean_object* v_f_84_, lean_object* v_xs_85_){
_start:
{
lean_object* v_head_86_; lean_object* v_tail_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_head_86_ = lean_ctor_get(v_xs_85_, 0);
lean_inc(v_head_86_);
v_tail_87_ = lean_ctor_get(v_xs_85_, 1);
lean_inc(v_tail_87_);
lean_dec(v_xs_85_);
v___f_88_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_88_, 0, v_inst_83_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_88_, v_f_84_, v_head_86_, v___x_89_, v___x_90_, v_tail_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn(lean_object* v_00_u03b2_92_, lean_object* v_00_u03b1_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_f_96_, lean_object* v_xs_97_, lean_object* v_h_98_){
_start:
{
lean_object* v_head_99_; lean_object* v_tail_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_head_99_ = lean_ctor_get(v_xs_97_, 0);
lean_inc(v_head_99_);
v_tail_100_ = lean_ctor_get(v_xs_97_, 1);
lean_inc(v_tail_100_);
lean_dec(v_xs_97_);
v___f_101_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_101_, 0, v_inst_95_);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_101_, v_f_96_, v_head_99_, v___x_102_, v___x_103_, v_tail_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f___redArg(lean_object* v_inst_105_, lean_object* v_f_106_, lean_object* v_xs_107_){
_start:
{
if (lean_obj_tag(v_xs_107_) == 0)
{
lean_object* v___x_108_; 
lean_dec(v_f_106_);
lean_dec_ref(v_inst_105_);
v___x_108_ = lean_box(0);
return v___x_108_;
}
else
{
lean_object* v_head_109_; lean_object* v_tail_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_head_109_ = lean_ctor_get(v_xs_107_, 0);
lean_inc(v_head_109_);
v_tail_110_ = lean_ctor_get(v_xs_107_, 1);
lean_inc(v_tail_110_);
lean_dec_ref_known(v_xs_107_, 2);
v___f_111_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_111_, 0, v_inst_105_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_111_, v_f_106_, v_head_109_, v___x_112_, v___x_113_, v_tail_110_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxIdxOn_x3f(lean_object* v_00_u03b2_116_, lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_f_120_, lean_object* v_xs_121_){
_start:
{
if (lean_obj_tag(v_xs_121_) == 0)
{
lean_object* v___x_122_; 
lean_dec(v_f_120_);
lean_dec_ref(v_inst_119_);
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v_head_123_; lean_object* v_tail_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_head_123_ = lean_ctor_get(v_xs_121_, 0);
lean_inc(v_head_123_);
v_tail_124_ = lean_ctor_get(v_xs_121_, 1);
lean_inc(v_tail_124_);
lean_dec_ref_known(v_xs_121_, 2);
v___f_125_ = lean_alloc_closure((void*)(l_List_maxIdxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_125_, 0, v_inst_119_);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_go___redArg(v___f_125_, v_f_120_, v_head_123_, v___x_126_, v___x_127_, v_tail_124_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter___redArg(lean_object* v_xs_130_, lean_object* v_h__1_131_){
_start:
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_134_; 
v_head_132_ = lean_ctor_get(v_xs_130_, 0);
lean_inc(v_head_132_);
v_tail_133_ = lean_ctor_get(v_xs_130_, 1);
lean_inc(v_tail_133_);
lean_dec(v_xs_130_);
v___x_134_ = lean_apply_3(v_h__1_131_, v_head_132_, v_tail_133_, lean_box(0));
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_minIdxOn_match__3_splitter(lean_object* v_00_u03b1_135_, lean_object* v_motive_136_, lean_object* v_xs_137_, lean_object* v_h_138_, lean_object* v_h__1_139_){
_start:
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_142_; 
v_head_140_ = lean_ctor_get(v_xs_137_, 0);
lean_inc(v_head_140_);
v_tail_141_ = lean_ctor_get(v_xs_137_, 1);
lean_inc(v_tail_141_);
lean_dec(v_xs_137_);
v___x_142_ = lean_apply_3(v_h__1_139_, v_head_140_, v_tail_141_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_xs_145_, lean_object* v_ys_146_, lean_object* v_i_147_, lean_object* v_j_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
lean_inc(v_i_147_);
v___x_149_ = l_List_get___redArg(v_xs_145_, v_i_147_);
lean_inc(v_f_144_);
v___x_150_ = lean_apply_1(v_f_144_, v___x_149_);
lean_inc(v_j_148_);
v___x_151_ = l_List_get___redArg(v_ys_146_, v_j_148_);
v___x_152_ = lean_apply_1(v_f_144_, v___x_151_);
v___x_153_ = lean_apply_2(v_inst_143_, v___x_150_, v___x_152_);
v___x_154_ = lean_unbox(v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec(v_i_147_);
v___x_155_ = l_List_lengthTR___redArg(v_xs_145_);
v___x_156_ = lean_nat_add(v___x_155_, v_j_148_);
lean_dec(v_j_148_);
lean_dec(v___x_155_);
return v___x_156_;
}
else
{
lean_dec(v_j_148_);
return v_i_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg___boxed(lean_object* v_inst_157_, lean_object* v_f_158_, lean_object* v_xs_159_, lean_object* v_ys_160_, lean_object* v_i_161_, lean_object* v_j_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(v_inst_157_, v_f_158_, v_xs_159_, v_ys_160_, v_i_161_, v_j_162_);
lean_dec(v_ys_160_);
lean_dec(v_xs_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(lean_object* v_00_u03b2_164_, lean_object* v_00_u03b1_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_f_168_, lean_object* v_xs_169_, lean_object* v_ys_170_, lean_object* v_i_171_, lean_object* v_j_172_, lean_object* v_hi_173_, lean_object* v_hj_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___redArg(v_inst_167_, v_f_168_, v_xs_169_, v_ys_170_, v_i_171_, v_j_172_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn___boxed(lean_object* v_00_u03b2_176_, lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_f_180_, lean_object* v_xs_181_, lean_object* v_ys_182_, lean_object* v_i_183_, lean_object* v_j_184_, lean_object* v_hi_185_, lean_object* v_hj_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Init_Data_List_MinMaxIdx_0__List_combineMinIdxOn(v_00_u03b2_176_, v_00_u03b1_177_, v_inst_178_, v_inst_179_, v_f_180_, v_xs_181_, v_ys_182_, v_i_183_, v_j_184_, v_hi_185_, v_hj_186_);
lean_dec(v_ys_182_);
lean_dec(v_xs_181_);
return v_res_187_;
}
}
lean_object* runtime_initialize_Init_Data_List_MinMaxOn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_MinMaxIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
