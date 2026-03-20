// Lean compiler output
// Module: Init.Data.List.MapIdx
// Imports: public import Init.Data.Option.Attach public import Init.Data.List.OfFn import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.List.Nat.Range import Init.Data.List.Nat.TakeDrop import Init.Data.List.Range import Init.Data.List.TakeDrop import Init.Data.Prod import Init.Data.Subtype.Basic import Init.Omega
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
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdx_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdx_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdx_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapFinIdx___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapFinIdx___redArg___closed__0 = (const lean_object*)&l_List_mapFinIdx___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapFinIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdxM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdxM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdxM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdxM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapFinIdx_go___redArg(lean_object* v_f_1_, lean_object* v_bs_2_, lean_object* v_acc_3_){
_start:
{
if (lean_obj_tag(v_bs_2_) == 0)
{
lean_object* v___x_4_; 
lean_dec(v_f_1_);
v___x_4_ = lean_array_to_list(v_acc_3_);
return v___x_4_;
}
else
{
lean_object* v_head_5_; lean_object* v_tail_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_head_5_ = lean_ctor_get(v_bs_2_, 0);
lean_inc(v_head_5_);
v_tail_6_ = lean_ctor_get(v_bs_2_, 1);
lean_inc(v_tail_6_);
lean_dec_ref(v_bs_2_);
v___x_7_ = lean_array_get_size(v_acc_3_);
lean_inc(v_f_1_);
v___x_8_ = lean_apply_3(v_f_1_, v___x_7_, v_head_5_, lean_box(0));
v___x_9_ = lean_array_push(v_acc_3_, v___x_8_);
v_bs_2_ = v_tail_6_;
v_acc_3_ = v___x_9_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdx_go(lean_object* v_00_u03b1_11_, lean_object* v_00_u03b2_12_, lean_object* v_as_13_, lean_object* v_f_14_, lean_object* v_bs_15_, lean_object* v_acc_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_List_mapFinIdx_go___redArg(v_f_14_, v_bs_15_, v_acc_16_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdx_go___boxed(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_as_21_, lean_object* v_f_22_, lean_object* v_bs_23_, lean_object* v_acc_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_List_mapFinIdx_go(v_00_u03b1_19_, v_00_u03b2_20_, v_as_21_, v_f_22_, v_bs_23_, v_acc_24_, v_a_25_);
lean_dec(v_as_21_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdx___redArg(lean_object* v_as_29_, lean_object* v_f_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_32_ = l_List_mapFinIdx_go___redArg(v_f_30_, v_as_29_, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdx(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_as_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_38_ = l_List_mapFinIdx_go___redArg(v_f_36_, v_as_35_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go___redArg(lean_object* v_f_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
if (lean_obj_tag(v_a_40_) == 0)
{
lean_object* v___x_42_; 
lean_dec(v_f_39_);
v___x_42_ = lean_array_to_list(v_a_41_);
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_head_43_ = lean_ctor_get(v_a_40_, 0);
lean_inc(v_head_43_);
v_tail_44_ = lean_ctor_get(v_a_40_, 1);
lean_inc(v_tail_44_);
lean_dec_ref(v_a_40_);
v___x_45_ = lean_array_get_size(v_a_41_);
lean_inc(v_f_39_);
v___x_46_ = lean_apply_2(v_f_39_, v___x_45_, v_head_43_);
v___x_47_ = lean_array_push(v_a_41_, v___x_46_);
v_a_40_ = v_tail_44_;
v_a_41_ = v___x_47_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdx_go(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_f_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_List_mapIdx_go___redArg(v_f_51_, v_a_52_, v_a_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx___redArg(lean_object* v_f_55_, lean_object* v_as_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_58_ = l_List_mapIdx_go___redArg(v_f_55_, v_as_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdx(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_f_61_, lean_object* v_as_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_64_ = l_List_mapIdx_go___redArg(v_f_61_, v_as_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___redArg(lean_object* v_inst_65_, lean_object* v_f_66_, lean_object* v_bs_67_, lean_object* v_acc_68_){
_start:
{
if (lean_obj_tag(v_bs_67_) == 0)
{
lean_object* v_toApplicative_69_; lean_object* v_toPure_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_toApplicative_69_ = lean_ctor_get(v_inst_65_, 0);
lean_inc_ref(v_toApplicative_69_);
lean_dec(v_f_66_);
lean_dec_ref(v_inst_65_);
v_toPure_70_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_70_);
lean_dec_ref(v_toApplicative_69_);
v___x_71_ = lean_array_to_list(v_acc_68_);
v___x_72_ = lean_apply_2(v_toPure_70_, lean_box(0), v___x_71_);
return v___x_72_;
}
else
{
lean_object* v_toBind_73_; lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_toBind_73_ = lean_ctor_get(v_inst_65_, 1);
lean_inc(v_toBind_73_);
v_head_74_ = lean_ctor_get(v_bs_67_, 0);
lean_inc(v_head_74_);
v_tail_75_ = lean_ctor_get(v_bs_67_, 1);
lean_inc(v_tail_75_);
lean_dec_ref(v_bs_67_);
lean_inc(v_f_66_);
lean_inc_ref(v_acc_68_);
v___f_76_ = lean_alloc_closure((void*)(l_List_mapFinIdxM_go___redArg___lam__0), 5, 4);
lean_closure_set(v___f_76_, 0, v_acc_68_);
lean_closure_set(v___f_76_, 1, v_inst_65_);
lean_closure_set(v___f_76_, 2, v_f_66_);
lean_closure_set(v___f_76_, 3, v_tail_75_);
v___x_77_ = lean_array_get_size(v_acc_68_);
lean_dec_ref(v_acc_68_);
v___x_78_ = lean_apply_3(v_f_66_, v___x_77_, v_head_74_, lean_box(0));
v___x_79_ = lean_apply_4(v_toBind_73_, lean_box(0), lean_box(0), v___x_78_, v___f_76_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___redArg___lam__0(lean_object* v_acc_80_, lean_object* v_inst_81_, lean_object* v_f_82_, lean_object* v_tail_83_, lean_object* v_____do__lift_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_array_push(v_acc_80_, v_____do__lift_84_);
v___x_86_ = l_List_mapFinIdxM_go___redArg(v_inst_81_, v_f_82_, v_tail_83_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go(lean_object* v_m_87_, lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_inst_90_, lean_object* v_as_91_, lean_object* v_f_92_, lean_object* v_bs_93_, lean_object* v_acc_94_, lean_object* v_a_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_List_mapFinIdxM_go___redArg(v_inst_90_, v_f_92_, v_bs_93_, v_acc_94_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM_go___boxed(lean_object* v_m_97_, lean_object* v_00_u03b1_98_, lean_object* v_00_u03b2_99_, lean_object* v_inst_100_, lean_object* v_as_101_, lean_object* v_f_102_, lean_object* v_bs_103_, lean_object* v_acc_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_List_mapFinIdxM_go(v_m_97_, v_00_u03b1_98_, v_00_u03b2_99_, v_inst_100_, v_as_101_, v_f_102_, v_bs_103_, v_acc_104_, v_a_105_);
lean_dec(v_as_101_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM___redArg(lean_object* v_inst_107_, lean_object* v_as_108_, lean_object* v_f_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_111_ = l_List_mapFinIdxM_go___redArg(v_inst_107_, v_f_109_, v_as_108_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_List_mapFinIdxM(lean_object* v_m_112_, lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_inst_115_, lean_object* v_as_116_, lean_object* v_f_117_){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_119_ = l_List_mapFinIdxM_go___redArg(v_inst_115_, v_f_117_, v_as_116_, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdxM_go___redArg(lean_object* v_inst_120_, lean_object* v_f_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
if (lean_obj_tag(v_a_122_) == 0)
{
lean_object* v_toApplicative_124_; lean_object* v_toPure_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_toApplicative_124_ = lean_ctor_get(v_inst_120_, 0);
lean_inc_ref(v_toApplicative_124_);
lean_dec(v_f_121_);
lean_dec_ref(v_inst_120_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_125_);
lean_dec_ref(v_toApplicative_124_);
v___x_126_ = lean_array_to_list(v_a_123_);
v___x_127_ = lean_apply_2(v_toPure_125_, lean_box(0), v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_toBind_128_; lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___f_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_toBind_128_ = lean_ctor_get(v_inst_120_, 1);
lean_inc(v_toBind_128_);
v_head_129_ = lean_ctor_get(v_a_122_, 0);
lean_inc(v_head_129_);
v_tail_130_ = lean_ctor_get(v_a_122_, 1);
lean_inc(v_tail_130_);
lean_dec_ref(v_a_122_);
lean_inc(v_f_121_);
lean_inc_ref(v_a_123_);
v___f_131_ = lean_alloc_closure((void*)(l_List_mapIdxM_go___redArg___lam__0), 5, 4);
lean_closure_set(v___f_131_, 0, v_a_123_);
lean_closure_set(v___f_131_, 1, v_inst_120_);
lean_closure_set(v___f_131_, 2, v_f_121_);
lean_closure_set(v___f_131_, 3, v_tail_130_);
v___x_132_ = lean_array_get_size(v_a_123_);
lean_dec_ref(v_a_123_);
v___x_133_ = lean_apply_2(v_f_121_, v___x_132_, v_head_129_);
v___x_134_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v___x_133_, v___f_131_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapIdxM_go___redArg___lam__0(lean_object* v_a_135_, lean_object* v_inst_136_, lean_object* v_f_137_, lean_object* v_tail_138_, lean_object* v_____do__lift_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_array_push(v_a_135_, v_____do__lift_139_);
v___x_141_ = l_List_mapIdxM_go___redArg(v_inst_136_, v_f_137_, v_tail_138_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdxM_go(lean_object* v_m_142_, lean_object* v_00_u03b1_143_, lean_object* v_00_u03b2_144_, lean_object* v_inst_145_, lean_object* v_f_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_List_mapIdxM_go___redArg(v_inst_145_, v_f_146_, v_a_147_, v_a_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdxM___redArg(lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_as_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_154_ = l_List_mapIdxM_go___redArg(v_inst_150_, v_f_151_, v_as_152_, v___x_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_List_mapIdxM(lean_object* v_m_155_, lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_inst_158_, lean_object* v_f_159_, lean_object* v_as_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_List_mapFinIdx___redArg___closed__0));
v___x_162_ = l_List_mapIdxM_go___redArg(v_inst_158_, v_f_159_, v_as_160_, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_h__2_166_);
v___x_167_ = lean_apply_2(v_h__1_165_, v_x_164_, lean_box(0));
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_165_);
v_head_168_ = lean_ctor_get(v_x_163_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_x_163_, 1);
lean_inc(v_tail_169_);
lean_dec_ref(v_x_163_);
v___x_170_ = lean_apply_4(v_h__2_166_, v_head_168_, v_tail_169_, v_x_164_, lean_box(0));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter(lean_object* v_00_u03b1_171_, lean_object* v_00_u03b2_172_, lean_object* v_as_173_, lean_object* v_motive_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_h__1_178_, lean_object* v_h__2_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___redArg(v_x_175_, v_x_176_, v_h__1_178_, v_h__2_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter___boxed(lean_object* v_00_u03b1_181_, lean_object* v_00_u03b2_182_, lean_object* v_as_183_, lean_object* v_motive_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_h__1_188_, lean_object* v_h__2_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l___private_Init_Data_List_MapIdx_0__List_mapFinIdx_go_match__1_splitter(v_00_u03b1_181_, v_00_u03b2_182_, v_as_183_, v_motive_184_, v_x_185_, v_x_186_, v_x_187_, v_h__1_188_, v_h__2_189_);
lean_dec(v_as_183_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
if (lean_obj_tag(v_x_191_) == 0)
{
lean_object* v___x_195_; 
lean_dec(v_h__2_194_);
v___x_195_ = lean_apply_1(v_h__1_193_, v_x_192_);
return v___x_195_;
}
else
{
lean_object* v_head_196_; lean_object* v_tail_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_193_);
v_head_196_ = lean_ctor_get(v_x_191_, 0);
lean_inc(v_head_196_);
v_tail_197_ = lean_ctor_get(v_x_191_, 1);
lean_inc(v_tail_197_);
lean_dec_ref(v_x_191_);
v___x_198_ = lean_apply_3(v_h__2_194_, v_head_196_, v_tail_197_, v_x_192_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter(lean_object* v_00_u03b1_199_, lean_object* v_00_u03b2_200_, lean_object* v_motive_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_h__1_204_, lean_object* v_h__2_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l___private_Init_Data_List_MapIdx_0__List_mapIdx_go_match__1_splitter___redArg(v_x_202_, v_x_203_, v_h__1_204_, v_h__2_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter___redArg(lean_object* v_opt_207_, lean_object* v_h__1_208_, lean_object* v_h__2_209_){
_start:
{
if (lean_obj_tag(v_opt_207_) == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_h__1_208_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_1(v_h__2_209_, v___x_210_);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; 
lean_dec(v_h__2_209_);
v_val_212_ = lean_ctor_get(v_opt_207_, 0);
lean_inc(v_val_212_);
lean_dec_ref(v_opt_207_);
v___x_213_ = lean_apply_1(v_h__1_208_, v_val_212_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter(lean_object* v_00_u03b1_214_, lean_object* v_motive_215_, lean_object* v_opt_216_, lean_object* v_h__1_217_, lean_object* v_h__2_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Init_Data_List_MapIdx_0__Option_getD_match__1_splitter___redArg(v_opt_216_, v_h__1_217_, v_h__2_218_);
return v___x_219_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_OfFn(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Subtype_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
lean_object* initialize_Init_Data_Subtype_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Subtype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_MapIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_MapIdx(builtin);
}
#ifdef __cplusplus
}
#endif
