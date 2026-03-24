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
LEAN_EXPORT uint8_t l_List_maxOn___redArg___lam__0(lean_object* v_inst_20_, lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_apply_2(v_inst_20_, v_b_22_, v_a_21_);
v___x_24_ = lean_unbox(v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_List_maxOn___redArg___lam__0___boxed(lean_object* v_inst_25_, lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_List_maxOn___redArg___lam__0(v_inst_25_, v_a_26_, v_b_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_List_maxOn___redArg(lean_object* v_inst_30_, lean_object* v_f_31_, lean_object* v_l_32_){
_start:
{
lean_object* v___x_33_; lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_33_ = lean_box(0);
v_head_34_ = lean_ctor_get(v_l_32_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_l_32_, 1);
lean_inc(v_tail_35_);
lean_dec(v_l_32_);
v___f_36_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_36_, 0, v_inst_30_);
v___x_37_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_37_, 0, lean_box(0));
lean_closure_set(v___x_37_, 1, lean_box(0));
lean_closure_set(v___x_37_, 2, v___x_33_);
lean_closure_set(v___x_37_, 3, v___f_36_);
lean_closure_set(v___x_37_, 4, v_f_31_);
v___x_38_ = l_List_foldl___redArg(v___x_37_, v_head_34_, v_tail_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_List_maxOn(lean_object* v_00_u03b2_39_, lean_object* v_00_u03b1_40_, lean_object* v_i_41_, lean_object* v_inst_42_, lean_object* v_f_43_, lean_object* v_l_44_, lean_object* v_h_45_){
_start:
{
lean_object* v___x_46_; lean_object* v_head_47_; lean_object* v_tail_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = lean_box(0);
v_head_47_ = lean_ctor_get(v_l_44_, 0);
lean_inc(v_head_47_);
v_tail_48_ = lean_ctor_get(v_l_44_, 1);
lean_inc(v_tail_48_);
lean_dec(v_l_44_);
v___f_49_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_49_, 0, v_inst_42_);
v___x_50_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_50_, 0, lean_box(0));
lean_closure_set(v___x_50_, 1, lean_box(0));
lean_closure_set(v___x_50_, 2, v___x_46_);
lean_closure_set(v___x_50_, 3, v___f_49_);
lean_closure_set(v___x_50_, 4, v_f_43_);
v___x_51_ = l_List_foldl___redArg(v___x_50_, v_head_47_, v_tail_48_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_List_minOn_x3f___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_f_54_, lean_object* v_l_55_){
_start:
{
if (lean_obj_tag(v_l_55_) == 0)
{
lean_object* v___x_56_; 
lean_dec(v_f_54_);
lean_dec_ref(v_inst_53_);
v___x_56_ = lean_box(0);
return v___x_56_;
}
else
{
lean_object* v_head_57_; lean_object* v_tail_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_head_57_ = lean_ctor_get(v_l_55_, 0);
lean_inc(v_head_57_);
v_tail_58_ = lean_ctor_get(v_l_55_, 1);
lean_inc(v_tail_58_);
lean_dec_ref(v_l_55_);
v___x_59_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_59_, 0, lean_box(0));
lean_closure_set(v___x_59_, 1, lean_box(0));
lean_closure_set(v___x_59_, 2, v_inst_52_);
lean_closure_set(v___x_59_, 3, v_inst_53_);
lean_closure_set(v___x_59_, 4, v_f_54_);
v___x_60_ = l_List_foldl___redArg(v___x_59_, v_head_57_, v_tail_58_);
v___x_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l_List_minOn_x3f(lean_object* v_00_u03b2_62_, lean_object* v_00_u03b1_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_f_66_, lean_object* v_l_67_){
_start:
{
if (lean_obj_tag(v_l_67_) == 0)
{
lean_object* v___x_68_; 
lean_dec(v_f_66_);
lean_dec_ref(v_inst_65_);
v___x_68_ = lean_box(0);
return v___x_68_;
}
else
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_head_69_ = lean_ctor_get(v_l_67_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_l_67_, 1);
lean_inc(v_tail_70_);
lean_dec_ref(v_l_67_);
v___x_71_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_71_, 0, lean_box(0));
lean_closure_set(v___x_71_, 1, lean_box(0));
lean_closure_set(v___x_71_, 2, v_inst_64_);
lean_closure_set(v___x_71_, 3, v_inst_65_);
lean_closure_set(v___x_71_, 4, v_f_66_);
v___x_72_ = l_List_foldl___redArg(v___x_71_, v_head_69_, v_tail_70_);
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxOn_x3f___redArg(lean_object* v_inst_74_, lean_object* v_f_75_, lean_object* v_l_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_box(0);
if (lean_obj_tag(v_l_76_) == 0)
{
lean_object* v___x_78_; 
lean_dec(v_f_75_);
lean_dec_ref(v_inst_74_);
v___x_78_ = lean_box(0);
return v___x_78_;
}
else
{
lean_object* v_head_79_; lean_object* v_tail_80_; lean_object* v___f_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_head_79_ = lean_ctor_get(v_l_76_, 0);
lean_inc(v_head_79_);
v_tail_80_ = lean_ctor_get(v_l_76_, 1);
lean_inc(v_tail_80_);
lean_dec_ref(v_l_76_);
v___f_81_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_81_, 0, v_inst_74_);
v___x_82_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_82_, 0, lean_box(0));
lean_closure_set(v___x_82_, 1, lean_box(0));
lean_closure_set(v___x_82_, 2, v___x_77_);
lean_closure_set(v___x_82_, 3, v___f_81_);
lean_closure_set(v___x_82_, 4, v_f_75_);
v___x_83_ = l_List_foldl___redArg(v___x_82_, v_head_79_, v_tail_80_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_List_maxOn_x3f(lean_object* v_00_u03b2_85_, lean_object* v_00_u03b1_86_, lean_object* v_i_87_, lean_object* v_inst_88_, lean_object* v_f_89_, lean_object* v_l_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_box(0);
if (lean_obj_tag(v_l_90_) == 0)
{
lean_object* v___x_92_; 
lean_dec(v_f_89_);
lean_dec_ref(v_inst_88_);
v___x_92_ = lean_box(0);
return v___x_92_;
}
else
{
lean_object* v_head_93_; lean_object* v_tail_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_head_93_ = lean_ctor_get(v_l_90_, 0);
lean_inc(v_head_93_);
v_tail_94_ = lean_ctor_get(v_l_90_, 1);
lean_inc(v_tail_94_);
lean_dec_ref(v_l_90_);
v___f_95_ = lean_alloc_closure((void*)(l_List_maxOn___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_95_, 0, v_inst_88_);
v___x_96_ = lean_alloc_closure((void*)(l_minOn), 7, 5);
lean_closure_set(v___x_96_, 0, lean_box(0));
lean_closure_set(v___x_96_, 1, lean_box(0));
lean_closure_set(v___x_96_, 2, v___x_91_);
lean_closure_set(v___x_96_, 3, v___f_95_);
lean_closure_set(v___x_96_, 4, v_f_89_);
v___x_97_ = l_List_foldl___redArg(v___x_96_, v_head_93_, v_tail_94_);
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter___redArg(lean_object* v_l_99_, lean_object* v_h__1_100_){
_start:
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_103_; 
v_head_101_ = lean_ctor_get(v_l_99_, 0);
lean_inc(v_head_101_);
v_tail_102_ = lean_ctor_get(v_l_99_, 1);
lean_inc(v_tail_102_);
lean_dec(v_l_99_);
v___x_103_ = lean_apply_3(v_h__1_100_, v_head_101_, v_tail_102_, lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_match__1_splitter(lean_object* v_00_u03b1_104_, lean_object* v_motive_105_, lean_object* v_l_106_, lean_object* v_h_107_, lean_object* v_h__1_108_){
_start:
{
lean_object* v_head_109_; lean_object* v_tail_110_; lean_object* v___x_111_; 
v_head_109_ = lean_ctor_get(v_l_106_, 0);
lean_inc(v_head_109_);
v_tail_110_ = lean_ctor_get(v_l_106_, 1);
lean_inc(v_tail_110_);
lean_dec(v_l_106_);
v___x_111_ = lean_apply_3(v_h__1_108_, v_head_109_, v_tail_110_, lean_box(0));
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter___redArg(lean_object* v_x_112_, lean_object* v_h__1_113_){
_start:
{
lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v___x_116_; 
v_head_114_ = lean_ctor_get(v_x_112_, 0);
lean_inc(v_head_114_);
v_tail_115_ = lean_ctor_get(v_x_112_, 1);
lean_inc(v_tail_115_);
lean_dec(v_x_112_);
v___x_116_ = lean_apply_3(v_h__1_113_, v_head_114_, v_tail_115_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_head_match__1_splitter(lean_object* v_00_u03b1_117_, lean_object* v_motive_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_h__1_121_){
_start:
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_124_; 
v_head_122_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_head_122_);
v_tail_123_ = lean_ctor_get(v_x_119_, 1);
lean_inc(v_tail_123_);
lean_dec(v_x_119_);
v___x_124_ = lean_apply_3(v_h__1_121_, v_head_122_, v_tail_123_, lean_box(0));
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter___redArg(lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_129_; 
lean_dec(v_h__2_128_);
v___x_129_ = lean_apply_1(v_h__1_127_, v_x_125_);
return v___x_129_;
}
else
{
lean_object* v_head_130_; lean_object* v_tail_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_127_);
v_head_130_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_head_130_);
v_tail_131_ = lean_ctor_get(v_x_126_, 1);
lean_inc(v_tail_131_);
lean_dec_ref(v_x_126_);
v___x_132_ = lean_apply_3(v_h__2_128_, v_x_125_, v_head_130_, v_tail_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_foldl_match__1_splitter(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_motive_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_h__1_138_, lean_object* v_h__2_139_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_140_; 
lean_dec(v_h__2_139_);
v___x_140_ = lean_apply_1(v_h__1_138_, v_x_136_);
return v___x_140_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v___x_143_; 
lean_dec(v_h__1_138_);
v_head_141_ = lean_ctor_get(v_x_137_, 0);
lean_inc(v_head_141_);
v_tail_142_ = lean_ctor_get(v_x_137_, 1);
lean_inc(v_tail_142_);
lean_dec_ref(v_x_137_);
v___x_143_ = lean_apply_3(v_h__2_139_, v_x_136_, v_head_141_, v_tail_142_);
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_146_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_apply_1(v_h__1_145_, v___x_147_);
return v___x_148_;
}
else
{
lean_object* v_head_149_; lean_object* v_tail_150_; lean_object* v___x_151_; 
lean_dec(v_h__1_145_);
v_head_149_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_head_149_);
v_tail_150_ = lean_ctor_get(v_x_144_, 1);
lean_inc(v_tail_150_);
lean_dec_ref(v_x_144_);
v___x_151_ = lean_apply_2(v_h__2_146_, v_head_149_, v_tail_150_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_getLast_x3f_match__1_splitter(lean_object* v_00_u03b1_152_, lean_object* v_motive_153_, lean_object* v_x_154_, lean_object* v_h__1_155_, lean_object* v_h__2_156_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__2_156_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__1_155_, v___x_157_);
return v___x_158_;
}
else
{
lean_object* v_head_159_; lean_object* v_tail_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_155_);
v_head_159_ = lean_ctor_get(v_x_154_, 0);
lean_inc(v_head_159_);
v_tail_160_ = lean_ctor_get(v_x_154_, 1);
lean_inc(v_tail_160_);
lean_dec_ref(v_x_154_);
v___x_161_ = lean_apply_2(v_h__2_156_, v_head_159_, v_tail_160_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter___redArg(lean_object* v_l_162_, lean_object* v_h__1_163_, lean_object* v_h__2_164_){
_start:
{
if (lean_obj_tag(v_l_162_) == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__2_164_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__1_163_, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v___x_169_; 
lean_dec(v_h__1_163_);
v_head_167_ = lean_ctor_get(v_l_162_, 0);
lean_inc(v_head_167_);
v_tail_168_ = lean_ctor_get(v_l_162_, 1);
lean_inc(v_tail_168_);
lean_dec_ref(v_l_162_);
v___x_169_ = lean_apply_2(v_h__2_164_, v_head_167_, v_tail_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMaxOn_0__List_minOn_x3f_match__1_splitter(lean_object* v_00_u03b1_170_, lean_object* v_motive_171_, lean_object* v_l_172_, lean_object* v_h__1_173_, lean_object* v_h__2_174_){
_start:
{
if (lean_obj_tag(v_l_172_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_174_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__1_173_, v___x_175_);
return v___x_176_;
}
else
{
lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_173_);
v_head_177_ = lean_ctor_get(v_l_172_, 0);
lean_inc(v_head_177_);
v_tail_178_ = lean_ctor_get(v_l_172_, 1);
lean_inc(v_tail_178_);
lean_dec_ref(v_l_172_);
v___x_179_ = lean_apply_2(v_h__2_174_, v_head_177_, v_tail_178_);
return v___x_179_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_MinMaxOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
