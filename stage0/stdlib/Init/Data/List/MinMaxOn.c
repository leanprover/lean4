// Lean compiler output
// Module: Init.Data.List.MinMaxOn
// Imports: public import Init.Data.Order.MinMaxOn public import Init.Data.List.Lemmas public import Init.Data.List.TakeDrop import Init.Data.Order.Lemmas import Init.Data.List.Sublist import Init.Data.List.MinMax public import Init.Data.Option.Lemmas import Init.ByCases import Init.Data.Bool
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
lean_object* l_minOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minOn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_maxOn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxOn___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxOn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minOn_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxOn_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_maxOn_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_minOn___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_f_3_, lean_object* v_l_4_){
_start:
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_head_5_ = lean_ctor_get(v_l_4_, 0);
lean_inc(v_head_5_);
v_tail_6_ = lean_ctor_get(v_l_4_, 1);
lean_inc(v_tail_6_);
lean_dec(v_l_4_);
v___x_7_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_7_, 0, lean_box(0));
lean_closure_set(v___x_7_, 1, lean_box(0));
lean_closure_set(v___x_7_, 2, v_inst_1_);
lean_closure_set(v___x_7_, 3, v_inst_2_);
lean_closure_set(v___x_7_, 4, v_f_3_);
v___x_8_ = l_List_foldl___redArg(v___x_7_, v_head_5_, v_tail_6_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_minOn(lean_object* v_00_u03b2_9_, lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_, lean_object* v_f_13_, lean_object* v_l_14_, lean_object* v_h_15_){
_start:
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_head_16_ = lean_ctor_get(v_l_14_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_l_14_, 1);
lean_inc(v_tail_17_);
lean_dec(v_l_14_);
v___x_18_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_18_, 0, lean_box(0));
lean_closure_set(v___x_18_, 1, lean_box(0));
lean_closure_set(v___x_18_, 2, v_inst_11_);
lean_closure_set(v___x_18_, 3, v_inst_12_);
lean_closure_set(v___x_18_, 4, v_f_13_);
v___x_19_ = l_List_foldl___redArg(v___x_18_, v_head_16_, v_tail_17_);
return v___x_19_;
}
}
uint8_t l_List_maxOn___redArg___lam__0(lean_object* v_inst_20_, lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_apply_2(v_inst_20_, v_b_22_, v_a_21_);
v___x_24_ = lean_unbox(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT void l_List_maxOn___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_20_ = stack[0].m_obj;
lean_object* v_a_21_ = stack[1].m_obj;
lean_object* v_b_22_ = stack[2].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_List_maxOn___redArg___lam__0(v_inst_20_, v_a_21_, v_b_22_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_List_maxOn___redArg___lam__0___boxed(lean_object* v_inst_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_List_maxOn___redArg___lam__0(v_inst_26_, v_a_27_, v_b_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT lean_object* l_List_maxOn___redArg(lean_object* v_inst_31_, lean_object* v_f_32_, lean_object* v_l_33_){
_start:
{
lean_object* v___x_34_; lean_object* v_head_35_; lean_object* v_tail_36_; lean_object* v___f_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_34_ = lean_box(0);
v_head_35_ = lean_ctor_get(v_l_33_, 0);
lean_inc(v_head_35_);
v_tail_36_ = lean_ctor_get(v_l_33_, 1);
lean_inc(v_tail_36_);
lean_dec(v_l_33_);
v___f_37_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_37_, 0, v_inst_31_);
v___x_38_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_38_, 0, lean_box(0));
lean_closure_set(v___x_38_, 1, lean_box(0));
lean_closure_set(v___x_38_, 2, v___x_34_);
lean_closure_set(v___x_38_, 3, v___f_37_);
lean_closure_set(v___x_38_, 4, v_f_32_);
v___x_39_ = l_List_foldl___redArg(v___x_38_, v_head_35_, v_tail_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_List_maxOn(lean_object* v_00_u03b2_40_, lean_object* v_00_u03b1_41_, lean_object* v_i_42_, lean_object* v_inst_43_, lean_object* v_f_44_, lean_object* v_l_45_, lean_object* v_h_46_){
_start:
{
lean_object* v___x_47_; lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_47_ = lean_box(0);
v_head_48_ = lean_ctor_get(v_l_45_, 0);
lean_inc(v_head_48_);
v_tail_49_ = lean_ctor_get(v_l_45_, 1);
lean_inc(v_tail_49_);
lean_dec(v_l_45_);
v___f_50_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_50_, 0, v_inst_43_);
v___x_51_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_51_, 0, lean_box(0));
lean_closure_set(v___x_51_, 1, lean_box(0));
lean_closure_set(v___x_51_, 2, v___x_47_);
lean_closure_set(v___x_51_, 3, v___f_50_);
lean_closure_set(v___x_51_, 4, v_f_44_);
v___x_52_ = l_List_foldl___redArg(v___x_51_, v_head_48_, v_tail_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_List_minOn_x3f___redArg(lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_f_55_, lean_object* v_l_56_){
_start:
{
if (lean_obj_tag(v_l_56_) == 0)
{
lean_object* v___x_57_; 
lean_dec(v_f_55_);
lean_dec_ref(v_inst_54_);
v___x_57_ = lean_box(0);
return v___x_57_;
}
else
{
lean_object* v_head_58_; lean_object* v_tail_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_head_58_ = lean_ctor_get(v_l_56_, 0);
lean_inc(v_head_58_);
v_tail_59_ = lean_ctor_get(v_l_56_, 1);
lean_inc(v_tail_59_);
lean_dec_ref_known(v_l_56_, 2);
v___x_60_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_60_, 0, lean_box(0));
lean_closure_set(v___x_60_, 1, lean_box(0));
lean_closure_set(v___x_60_, 2, v_inst_53_);
lean_closure_set(v___x_60_, 3, v_inst_54_);
lean_closure_set(v___x_60_, 4, v_f_55_);
v___x_61_ = l_List_foldl___redArg(v___x_60_, v_head_58_, v_tail_59_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_List_minOn_x3f(lean_object* v_00_u03b2_63_, lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_f_67_, lean_object* v_l_68_){
_start:
{
if (lean_obj_tag(v_l_68_) == 0)
{
lean_object* v___x_69_; 
lean_dec(v_f_67_);
lean_dec_ref(v_inst_66_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_head_70_; lean_object* v_tail_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_head_70_ = lean_ctor_get(v_l_68_, 0);
lean_inc(v_head_70_);
v_tail_71_ = lean_ctor_get(v_l_68_, 1);
lean_inc(v_tail_71_);
lean_dec_ref_known(v_l_68_, 2);
v___x_72_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_72_, 0, lean_box(0));
lean_closure_set(v___x_72_, 1, lean_box(0));
lean_closure_set(v___x_72_, 2, v_inst_65_);
lean_closure_set(v___x_72_, 3, v_inst_66_);
lean_closure_set(v___x_72_, 4, v_f_67_);
v___x_73_ = l_List_foldl___redArg(v___x_72_, v_head_70_, v_tail_71_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxOn_x3f___redArg(lean_object* v_inst_75_, lean_object* v_f_76_, lean_object* v_l_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(0);
if (lean_obj_tag(v_l_77_) == 0)
{
lean_object* v___x_79_; 
lean_dec(v_f_76_);
lean_dec_ref(v_inst_75_);
v___x_79_ = lean_box(0);
return v___x_79_;
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v_head_80_ = lean_ctor_get(v_l_77_, 0);
lean_inc(v_head_80_);
v_tail_81_ = lean_ctor_get(v_l_77_, 1);
lean_inc(v_tail_81_);
lean_dec_ref_known(v_l_77_, 2);
v___f_82_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_82_, 0, v_inst_75_);
v___x_83_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_83_, 0, lean_box(0));
lean_closure_set(v___x_83_, 1, lean_box(0));
lean_closure_set(v___x_83_, 2, v___x_78_);
lean_closure_set(v___x_83_, 3, v___f_82_);
lean_closure_set(v___x_83_, 4, v_f_76_);
v___x_84_ = l_List_foldl___redArg(v___x_83_, v_head_80_, v_tail_81_);
v___x_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxOn_x3f(lean_object* v_00_u03b2_86_, lean_object* v_00_u03b1_87_, lean_object* v_i_88_, lean_object* v_inst_89_, lean_object* v_f_90_, lean_object* v_l_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
if (lean_obj_tag(v_l_91_) == 0)
{
lean_object* v___x_93_; 
lean_dec(v_f_90_);
lean_dec_ref(v_inst_89_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v_head_94_; lean_object* v_tail_95_; lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_head_94_ = lean_ctor_get(v_l_91_, 0);
lean_inc(v_head_94_);
v_tail_95_ = lean_ctor_get(v_l_91_, 1);
lean_inc(v_tail_95_);
lean_dec_ref_known(v_l_91_, 2);
v___f_96_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_96_, 0, v_inst_89_);
v___x_97_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, lean_box(0));
lean_closure_set(v___x_97_, 2, v___x_92_);
lean_closure_set(v___x_97_, 3, v___f_96_);
lean_closure_set(v___x_97_, 4, v_f_90_);
v___x_98_ = l_List_foldl___redArg(v___x_97_, v_head_94_, v_tail_95_);
v___x_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter___redArg(lean_object* v_l_100_, lean_object* v_h__1_101_){
_start:
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_104_; 
v_head_102_ = lean_ctor_get(v_l_100_, 0);
lean_inc(v_head_102_);
v_tail_103_ = lean_ctor_get(v_l_100_, 1);
lean_inc(v_tail_103_);
lean_dec(v_l_100_);
v___x_104_ = lean_apply_3(v_h__1_101_, v_head_102_, v_tail_103_, lean_box(0));
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter(lean_object* v_00_u03b1_105_, lean_object* v_motive_106_, lean_object* v_l_107_, lean_object* v_h_108_, lean_object* v_h__1_109_){
_start:
{
lean_object* v_head_110_; lean_object* v_tail_111_; lean_object* v___x_112_; 
v_head_110_ = lean_ctor_get(v_l_107_, 0);
lean_inc(v_head_110_);
v_tail_111_ = lean_ctor_get(v_l_107_, 1);
lean_inc(v_tail_111_);
lean_dec(v_l_107_);
v___x_112_ = lean_apply_3(v_h__1_109_, v_head_110_, v_tail_111_, lean_box(0));
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter___redArg(lean_object* v_x_113_, lean_object* v_h__1_114_){
_start:
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v___x_117_; 
v_head_115_ = lean_ctor_get(v_x_113_, 0);
lean_inc(v_head_115_);
v_tail_116_ = lean_ctor_get(v_x_113_, 1);
lean_inc(v_tail_116_);
lean_dec(v_x_113_);
v___x_117_ = lean_apply_3(v_h__1_114_, v_head_115_, v_tail_116_, lean_box(0));
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter(lean_object* v_00_u03b1_118_, lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_h__1_122_){
_start:
{
lean_object* v_head_123_; lean_object* v_tail_124_; lean_object* v___x_125_; 
v_head_123_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_head_123_);
v_tail_124_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_tail_124_);
lean_dec(v_x_120_);
v___x_125_ = lean_apply_3(v_h__1_122_, v_head_123_, v_tail_124_, lean_box(0));
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter___redArg(lean_object* v_x_126_, lean_object* v_x_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_130_; 
lean_dec(v_h__2_129_);
v___x_130_ = lean_apply_1(v_h__1_128_, v_x_126_);
return v___x_130_;
}
else
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v___x_133_; 
lean_dec(v_h__1_128_);
v_head_131_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_head_131_);
v_tail_132_ = lean_ctor_get(v_x_127_, 1);
lean_inc(v_tail_132_);
lean_dec_ref_known(v_x_127_, 2);
v___x_133_ = lean_apply_3(v_h__2_129_, v_x_126_, v_head_131_, v_tail_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter(lean_object* v_00_u03b1_134_, lean_object* v_00_u03b2_135_, lean_object* v_motive_136_, lean_object* v_x_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v___x_141_; 
lean_dec(v_h__2_140_);
v___x_141_ = lean_apply_1(v_h__1_139_, v_x_137_);
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_139_);
v_head_142_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_head_142_);
v_tail_143_ = lean_ctor_get(v_x_138_, 1);
lean_inc(v_tail_143_);
lean_dec_ref_known(v_x_138_, 2);
v___x_144_ = lean_apply_3(v_h__2_140_, v_x_137_, v_head_142_, v_tail_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_h__2_147_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_apply_1(v_h__1_146_, v___x_148_);
return v___x_149_;
}
else
{
lean_object* v_head_150_; lean_object* v_tail_151_; lean_object* v___x_152_; 
lean_dec(v_h__1_146_);
v_head_150_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_head_150_);
v_tail_151_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_tail_151_);
lean_dec_ref_known(v_x_145_, 2);
v___x_152_ = lean_apply_2(v_h__2_147_, v_head_150_, v_tail_151_);
return v___x_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_153_, lean_object* v_motive_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_157_);
v___x_158_ = lean_box(0);
v___x_159_ = lean_apply_1(v_h__1_156_, v___x_158_);
return v___x_159_;
}
else
{
lean_object* v_head_160_; lean_object* v_tail_161_; lean_object* v___x_162_; 
lean_dec(v_h__1_156_);
v_head_160_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_head_160_);
v_tail_161_ = lean_ctor_get(v_x_155_, 1);
lean_inc(v_tail_161_);
lean_dec_ref_known(v_x_155_, 2);
v___x_162_ = lean_apply_2(v_h__2_157_, v_head_160_, v_tail_161_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter___redArg(lean_object* v_l_163_, lean_object* v_h__1_164_, lean_object* v_h__2_165_){
_start:
{
if (lean_obj_tag(v_l_163_) == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_h__2_165_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_1(v_h__1_164_, v___x_166_);
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_164_);
v_head_168_ = lean_ctor_get(v_l_163_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_l_163_, 1);
lean_inc(v_tail_169_);
lean_dec_ref_known(v_l_163_, 2);
v___x_170_ = lean_apply_2(v_h__2_165_, v_head_168_, v_tail_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter(lean_object* v_00_u03b1_171_, lean_object* v_motive_172_, lean_object* v_l_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
if (lean_obj_tag(v_l_173_) == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_h__2_175_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__1_174_, v___x_176_);
return v___x_177_;
}
else
{
lean_object* v_head_178_; lean_object* v_tail_179_; lean_object* v___x_180_; 
lean_dec(v_h__1_174_);
v_head_178_ = lean_ctor_get(v_l_173_, 0);
lean_inc(v_head_178_);
v_tail_179_ = lean_ctor_get(v_l_173_, 1);
lean_inc(v_tail_179_);
lean_dec_ref_known(v_l_173_, 2);
v___x_180_ = lean_apply_2(v_h__2_175_, v_head_178_, v_tail_179_);
return v___x_180_;
}
}
}
lean_object* runtime_initialize_Init_Data_Order_MinMaxOn(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_MinMaxOn(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_MinMaxOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_MinMaxOn(builtin);
}
#ifdef __cplusplus
}
#endif
