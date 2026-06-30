// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Lambda
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.InstantiateS
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkLambdaFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v_b_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
lean_inc(v___y_11_);
lean_inc_ref(v___y_10_);
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc(v___y_2_);
v___x_13_ = lean_apply_11(v_k_1_, v_b_7_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, lean_box(0));
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v_b_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0(v_k_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v_b_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec(v___y_16_);
lean_dec(v___y_15_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(lean_object* v_name_27_, uint8_t v_bi_28_, lean_object* v_type_29_, lean_object* v_k_30_, uint8_t v_kind_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v___f_42_; lean_object* v___x_43_; 
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
v___f_42_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_42_, 0, v_k_30_);
lean_closure_set(v___f_42_, 1, v___y_32_);
lean_closure_set(v___f_42_, 2, v___y_33_);
lean_closure_set(v___f_42_, 3, v___y_34_);
lean_closure_set(v___f_42_, 4, v___y_35_);
lean_closure_set(v___f_42_, 5, v___y_36_);
v___x_43_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_27_, v_bi_28_, v_type_29_, v___f_42_, v_kind_31_, v___y_37_, v___y_38_, v___y_39_, v___y_40_);
if (lean_obj_tag(v___x_43_) == 0)
{
return v___x_43_;
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg___boxed(lean_object* v_name_52_, lean_object* v_bi_53_, lean_object* v_type_54_, lean_object* v_k_55_, lean_object* v_kind_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
uint8_t v_bi_boxed_67_; uint8_t v_kind_boxed_68_; lean_object* v_res_69_; 
v_bi_boxed_67_ = lean_unbox(v_bi_53_);
v_kind_boxed_68_ = lean_unbox(v_kind_56_);
v_res_69_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_name_52_, v_bi_boxed_67_, v_type_54_, v_k_55_, v_kind_boxed_68_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec(v___y_58_);
lean_dec(v___y_57_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(lean_object* v_00_u03b1_70_, lean_object* v_name_71_, uint8_t v_bi_72_, lean_object* v_type_73_, lean_object* v_k_74_, uint8_t v_kind_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_name_71_, v_bi_72_, v_type_73_, v_k_74_, v_kind_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___boxed(lean_object* v_00_u03b1_87_, lean_object* v_name_88_, lean_object* v_bi_89_, lean_object* v_type_90_, lean_object* v_k_91_, lean_object* v_kind_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
uint8_t v_bi_boxed_103_; uint8_t v_kind_boxed_104_; lean_object* v_res_105_; 
v_bi_boxed_103_ = lean_unbox(v_bi_89_);
v_kind_boxed_104_ = lean_unbox(v_kind_92_);
v_res_105_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0(v_00_u03b1_87_, v_name_88_, v_bi_boxed_103_, v_type_90_, v_k_91_, v_kind_boxed_104_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec(v___y_94_);
lean_dec(v___y_93_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed(lean_object* v_fvars_106_, lean_object* v_body_107_, lean_object* v_modified_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
uint8_t v_modified_boxed_120_; lean_object* v_res_121_; 
v_modified_boxed_120_ = lean_unbox(v_modified_108_);
v_res_121_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(v_fvars_106_, v_body_107_, v_modified_boxed_120_, v_x_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec(v___y_111_);
lean_dec(v___y_110_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(lean_object* v_fvars_122_, lean_object* v_body_123_, lean_object* v_x_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_array_push(v_fvars_122_, v_x_124_);
v___x_136_ = 1;
v___x_137_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_body_123_, v___x_135_, v___x_136_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed(lean_object* v_fvars_138_, lean_object* v_body_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1(v_fvars_138_, v_body_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec(v___y_142_);
lean_dec(v___y_141_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(lean_object* v_e_152_, lean_object* v_fvars_153_, uint8_t v_modified_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
if (lean_obj_tag(v_e_152_) == 6)
{
lean_object* v_binderName_165_; lean_object* v_binderType_166_; lean_object* v_body_167_; uint8_t v_binderInfo_168_; lean_object* v___x_169_; 
v_binderName_165_ = lean_ctor_get(v_e_152_, 0);
lean_inc(v_binderName_165_);
v_binderType_166_ = lean_ctor_get(v_e_152_, 1);
lean_inc_ref(v_binderType_166_);
v_body_167_ = lean_ctor_get(v_e_152_, 2);
lean_inc_ref(v_body_167_);
v_binderInfo_168_ = lean_ctor_get_uint8(v_e_152_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_152_, 3);
v___x_169_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_binderType_166_, v_fvars_153_, v_a_159_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_n(v_a_170_, 2);
lean_dec_ref_known(v___x_169_, 1);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc_ref(v_a_160_);
lean_inc(v_a_159_);
lean_inc_ref(v_a_158_);
lean_inc(v_a_157_);
lean_inc(v_a_156_);
lean_inc(v_a_155_);
v___x_171_ = lean_sym_dsimp(v_a_170_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
lean_inc(v_a_172_);
lean_dec_ref_known(v___x_171_, 1);
if (lean_obj_tag(v_a_172_) == 0)
{
lean_object* v___x_173_; lean_object* v___f_174_; uint8_t v___x_175_; lean_object* v___x_176_; 
lean_dec_ref_known(v_a_172_, 0);
v___x_173_ = lean_box(v_modified_154_);
v___f_174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_174_, 0, v_fvars_153_);
lean_closure_set(v___f_174_, 1, v_body_167_);
lean_closure_set(v___f_174_, 2, v___x_173_);
v___x_175_ = 0;
v___x_176_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_binderName_165_, v_binderInfo_168_, v_a_170_, v___f_174_, v___x_175_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
return v___x_176_;
}
else
{
lean_object* v_e_x27_177_; lean_object* v___f_178_; uint8_t v___x_179_; lean_object* v___x_180_; 
lean_dec(v_a_170_);
v_e_x27_177_ = lean_ctor_get(v_a_172_, 0);
lean_inc_ref(v_e_x27_177_);
lean_dec_ref_known(v_a_172_, 1);
v___f_178_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_178_, 0, v_fvars_153_);
lean_closure_set(v___f_178_, 1, v_body_167_);
v___x_179_ = 0;
v___x_180_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go_spec__0___redArg(v_binderName_165_, v_binderInfo_168_, v_e_x27_177_, v___f_178_, v___x_179_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
return v___x_180_;
}
}
else
{
lean_dec(v_a_170_);
lean_dec_ref(v_body_167_);
lean_dec(v_binderName_165_);
lean_dec_ref(v_fvars_153_);
return v___x_171_;
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v_body_167_);
lean_dec(v_binderName_165_);
lean_dec_ref(v_fvars_153_);
v_a_181_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_169_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_169_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v___x_189_; 
lean_inc_ref(v_e_152_);
v___x_189_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_152_, v_fvars_153_, v_a_159_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc_ref(v_a_160_);
lean_inc(v_a_159_);
lean_inc_ref(v_a_158_);
lean_inc(v_a_157_);
lean_inc(v_a_156_);
lean_inc(v_a_155_);
v___x_191_ = lean_sym_dsimp(v_a_190_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_251_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_251_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_251_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_251_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
if (lean_obj_tag(v_a_192_) == 0)
{
lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_224_; 
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_224_ == 0)
{
v___x_197_ = v_a_192_;
v_isShared_198_ = v_isSharedCheck_224_;
goto v_resetjp_196_;
}
else
{
lean_dec(v_a_192_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_224_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
if (v_modified_154_ == 0)
{
lean_object* v___x_200_; 
lean_dec_ref(v_fvars_153_);
lean_dec_ref(v_e_152_);
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 0, 1);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
lean_ctor_set_uint8(v___x_200_, 0, v_modified_154_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 0, v___x_200_);
v___x_202_ = v___x_194_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v___x_205_; 
lean_del_object(v___x_197_);
lean_del_object(v___x_194_);
v___x_205_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_fvars_153_, v_e_152_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec_ref(v_fvars_153_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = 0;
v___x_211_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_211_, 0, v_a_206_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_210_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_205_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_205_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
}
else
{
lean_object* v_e_x27_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_250_; 
lean_del_object(v___x_194_);
lean_dec_ref(v_e_152_);
v_e_x27_225_ = lean_ctor_get(v_a_192_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_a_192_);
if (v_isSharedCheck_250_ == 0)
{
v___x_227_ = v_a_192_;
v_isShared_228_ = v_isSharedCheck_250_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_e_x27_225_);
lean_dec(v_a_192_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_250_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Sym_mkLambdaFVarsS(v_fvars_153_, v_e_x27_225_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec_ref(v_fvars_153_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_241_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_241_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_241_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_241_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; lean_object* v___x_236_; 
v___x_234_ = 0;
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v_a_230_);
v___x_236_ = v___x_227_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_230_);
v___x_236_ = v_reuseFailAlloc_240_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_236_);
v___x_238_ = v___x_232_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_del_object(v___x_227_);
v_a_242_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_229_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_229_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_153_);
lean_dec_ref(v_e_152_);
return v___x_191_;
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
lean_dec_ref(v_fvars_153_);
lean_dec_ref(v_e_152_);
v_a_252_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_189_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_189_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___lam__0(lean_object* v_fvars_260_, lean_object* v_body_261_, uint8_t v_modified_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_array_push(v_fvars_260_, v_x_263_);
v___x_275_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_body_261_, v___x_274_, v_modified_262_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go___boxed(lean_object* v_e_276_, lean_object* v_fvars_277_, lean_object* v_modified_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
uint8_t v_modified_boxed_289_; lean_object* v_res_290_; 
v_modified_boxed_289_ = lean_unbox(v_modified_278_);
v_res_290_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_e_276_, v_fvars_277_, v_modified_boxed_289_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec(v_a_280_);
lean_dec(v_a_279_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda(lean_object* v_e_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpLambda___closed__0));
v___x_305_ = 0;
v___x_306_ = l___private_Lean_Meta_Sym_DSimp_Lambda_0__Lean_Meta_Sym_DSimp_dsimpLambda_go(v_e_293_, v___x_304_, v___x_305_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLambda___boxed(lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Meta_Sym_DSimp_dsimpLambda(v_e_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec(v_a_309_);
lean_dec(v_a_308_);
return v_res_318_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Lambda(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Lambda(builtin);
}
#ifdef __cplusplus
}
#endif
