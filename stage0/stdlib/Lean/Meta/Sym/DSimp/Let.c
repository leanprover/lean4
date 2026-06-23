// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Let
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_sym_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v_b_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_k_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v_b_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v_b_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(lean_object* v_name_27_, lean_object* v_type_28_, lean_object* v_val_29_, lean_object* v_k_30_, uint8_t v_nondep_31_, uint8_t v_kind_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc(v___y_34_);
lean_inc(v___y_33_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_43_, 0, v_k_30_);
lean_closure_set(v___f_43_, 1, v___y_33_);
lean_closure_set(v___f_43_, 2, v___y_34_);
lean_closure_set(v___f_43_, 3, v___y_35_);
lean_closure_set(v___f_43_, 4, v___y_36_);
lean_closure_set(v___f_43_, 5, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_27_, v_type_28_, v_val_29_, v___f_43_, v_nondep_31_, v_kind_32_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(lean_object* v_name_53_, lean_object* v_type_54_, lean_object* v_val_55_, lean_object* v_k_56_, lean_object* v_nondep_57_, lean_object* v_kind_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
uint8_t v_nondep_boxed_69_; uint8_t v_kind_boxed_70_; lean_object* v_res_71_; 
v_nondep_boxed_69_ = lean_unbox(v_nondep_57_);
v_kind_boxed_70_ = lean_unbox(v_kind_58_);
v_res_71_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_53_, v_type_54_, v_val_55_, v_k_56_, v_nondep_boxed_69_, v_kind_boxed_70_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec(v___y_60_);
lean_dec(v___y_59_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(lean_object* v_00_u03b1_72_, lean_object* v_name_73_, lean_object* v_type_74_, lean_object* v_val_75_, lean_object* v_k_76_, uint8_t v_nondep_77_, uint8_t v_kind_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_73_, v_type_74_, v_val_75_, v_k_76_, v_nondep_77_, v_kind_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_90_ = _args[0];
lean_object* v_name_91_ = _args[1];
lean_object* v_type_92_ = _args[2];
lean_object* v_val_93_ = _args[3];
lean_object* v_k_94_ = _args[4];
lean_object* v_nondep_95_ = _args[5];
lean_object* v_kind_96_ = _args[6];
lean_object* v___y_97_ = _args[7];
lean_object* v___y_98_ = _args[8];
lean_object* v___y_99_ = _args[9];
lean_object* v___y_100_ = _args[10];
lean_object* v___y_101_ = _args[11];
lean_object* v___y_102_ = _args[12];
lean_object* v___y_103_ = _args[13];
lean_object* v___y_104_ = _args[14];
lean_object* v___y_105_ = _args[15];
lean_object* v___y_106_ = _args[16];
_start:
{
uint8_t v_nondep_boxed_107_; uint8_t v_kind_boxed_108_; lean_object* v_res_109_; 
v_nondep_boxed_107_ = lean_unbox(v_nondep_95_);
v_kind_boxed_108_ = lean_unbox(v_kind_96_);
v_res_109_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_90_, v_name_91_, v_type_92_, v_val_93_, v_k_94_, v_nondep_boxed_107_, v_kind_boxed_108_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec(v___y_98_);
lean_dec(v___y_97_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(lean_object* v_fvars_110_, lean_object* v_body_111_, lean_object* v_modified_112_, lean_object* v_x_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
uint8_t v_modified_boxed_124_; lean_object* v_res_125_; 
v_modified_boxed_124_ = lean_unbox(v_modified_112_);
v_res_125_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(v_fvars_110_, v_body_111_, v_modified_boxed_124_, v_x_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec(v___y_115_);
lean_dec(v___y_114_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(lean_object* v_fvars_126_, lean_object* v_body_127_, lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_array_push(v_fvars_126_, v_x_128_);
v___x_140_ = 1;
v___x_141_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_127_, v___x_139_, v___x_140_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(lean_object* v_fvars_142_, lean_object* v_body_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(v_fvars_142_, v_body_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec(v___y_146_);
lean_dec(v___y_145_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(lean_object* v_e_156_, lean_object* v_fvars_157_, uint8_t v_modified_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
if (lean_obj_tag(v_e_156_) == 8)
{
lean_object* v_declName_169_; lean_object* v_type_170_; lean_object* v_value_171_; lean_object* v_body_172_; uint8_t v_nondep_173_; lean_object* v___x_174_; 
v_declName_169_ = lean_ctor_get(v_e_156_, 0);
lean_inc(v_declName_169_);
v_type_170_ = lean_ctor_get(v_e_156_, 1);
lean_inc_ref(v_type_170_);
v_value_171_ = lean_ctor_get(v_e_156_, 2);
lean_inc_ref(v_value_171_);
v_body_172_ = lean_ctor_get(v_e_156_, 3);
lean_inc_ref(v_body_172_);
v_nondep_173_ = lean_ctor_get_uint8(v_e_156_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_156_, 4);
v___x_174_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_type_170_, v_fvars_157_, v_a_163_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_value_171_, v_fvars_157_, v_a_163_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_178_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc(v_a_160_);
lean_inc(v_a_159_);
lean_inc(v_a_175_);
v___x_178_ = lean_sym_dsimp(v_a_175_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc(v_a_160_);
lean_inc(v_a_159_);
lean_inc(v_a_177_);
v___x_180_ = lean_sym_dsimp(v_a_177_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_180_) == 0)
{
if (lean_obj_tag(v_a_179_) == 0)
{
lean_object* v_a_181_; 
lean_dec_ref_known(v_a_179_, 0);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_a_181_) == 0)
{
lean_object* v___x_182_; lean_object* v___f_183_; uint8_t v___x_184_; lean_object* v___x_185_; 
lean_dec_ref_known(v_a_181_, 0);
v___x_182_ = lean_box(v_modified_158_);
v___f_183_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed), 14, 3);
lean_closure_set(v___f_183_, 0, v_fvars_157_);
lean_closure_set(v___f_183_, 1, v_body_172_);
lean_closure_set(v___f_183_, 2, v___x_182_);
v___x_184_ = 0;
v___x_185_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_169_, v_a_175_, v_a_177_, v___f_183_, v_nondep_173_, v___x_184_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_185_;
}
else
{
lean_object* v_e_x27_186_; lean_object* v___f_187_; uint8_t v___x_188_; lean_object* v___x_189_; 
lean_dec(v_a_177_);
v_e_x27_186_ = lean_ctor_get(v_a_181_, 0);
lean_inc_ref(v_e_x27_186_);
lean_dec_ref_known(v_a_181_, 1);
v___f_187_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_187_, 0, v_fvars_157_);
lean_closure_set(v___f_187_, 1, v_body_172_);
v___x_188_ = 0;
v___x_189_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_169_, v_a_175_, v_e_x27_186_, v___f_187_, v_nondep_173_, v___x_188_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_189_;
}
}
else
{
lean_object* v_a_190_; 
lean_dec(v_a_175_);
v_a_190_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_180_, 1);
if (lean_obj_tag(v_a_190_) == 0)
{
lean_object* v_e_x27_191_; lean_object* v___f_192_; uint8_t v___x_193_; lean_object* v___x_194_; 
lean_dec_ref_known(v_a_190_, 0);
v_e_x27_191_ = lean_ctor_get(v_a_179_, 0);
lean_inc_ref(v_e_x27_191_);
lean_dec_ref_known(v_a_179_, 1);
v___f_192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_192_, 0, v_fvars_157_);
lean_closure_set(v___f_192_, 1, v_body_172_);
v___x_193_ = 0;
v___x_194_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_169_, v_e_x27_191_, v_a_177_, v___f_192_, v_nondep_173_, v___x_193_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_194_;
}
else
{
lean_object* v_e_x27_195_; lean_object* v_e_x27_196_; lean_object* v___f_197_; uint8_t v___x_198_; lean_object* v___x_199_; 
lean_dec(v_a_177_);
v_e_x27_195_ = lean_ctor_get(v_a_179_, 0);
lean_inc_ref(v_e_x27_195_);
lean_dec_ref_known(v_a_179_, 1);
v_e_x27_196_ = lean_ctor_get(v_a_190_, 0);
lean_inc_ref(v_e_x27_196_);
lean_dec_ref_known(v_a_190_, 1);
v___f_197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed), 13, 2);
lean_closure_set(v___f_197_, 0, v_fvars_157_);
lean_closure_set(v___f_197_, 1, v_body_172_);
v___x_198_ = 0;
v___x_199_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_169_, v_e_x27_195_, v_e_x27_196_, v___f_197_, v_nondep_173_, v___x_198_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
return v___x_199_;
}
}
}
else
{
lean_dec(v_a_179_);
lean_dec(v_a_177_);
lean_dec(v_a_175_);
lean_dec_ref(v_body_172_);
lean_dec(v_declName_169_);
lean_dec_ref(v_fvars_157_);
return v___x_180_;
}
}
else
{
lean_dec(v_a_177_);
lean_dec(v_a_175_);
lean_dec_ref(v_body_172_);
lean_dec(v_declName_169_);
lean_dec_ref(v_fvars_157_);
return v___x_178_;
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_175_);
lean_dec_ref(v_body_172_);
lean_dec(v_declName_169_);
lean_dec_ref(v_fvars_157_);
v_a_200_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_176_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_176_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_body_172_);
lean_dec_ref(v_value_171_);
lean_dec(v_declName_169_);
lean_dec_ref(v_fvars_157_);
v_a_208_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_174_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_174_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v___x_216_; 
lean_inc_ref(v_e_156_);
v___x_216_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_e_156_, v_fvars_157_, v_a_163_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_218_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_a_217_);
lean_dec_ref_known(v___x_216_, 1);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc(v_a_160_);
lean_inc(v_a_159_);
v___x_218_ = lean_sym_dsimp(v_a_217_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_280_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_280_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_280_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_280_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
if (lean_obj_tag(v_a_219_) == 0)
{
lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_252_; 
v_isSharedCheck_252_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_252_ == 0)
{
v___x_224_ = v_a_219_;
v_isShared_225_ = v_isSharedCheck_252_;
goto v_resetjp_223_;
}
else
{
lean_dec(v_a_219_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_252_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
if (v_modified_158_ == 0)
{
lean_object* v___x_227_; 
lean_dec_ref(v_fvars_157_);
lean_dec_ref(v_e_156_);
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 0, 1);
v___x_227_ = v_reuseFailAlloc_231_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_229_; 
lean_ctor_set_uint8(v___x_227_, 0, v_modified_158_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_229_ = v___x_221_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
else
{
uint8_t v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; 
lean_del_object(v___x_224_);
lean_del_object(v___x_221_);
v___x_232_ = 0;
v___x_233_ = 1;
v___x_234_ = l_Lean_Meta_mkLetFVars(v_fvars_157_, v_e_156_, v___x_232_, v___x_232_, v___x_233_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec_ref(v_fvars_157_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_243_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_243_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_243_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_239_, 0, v_a_235_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_232_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_241_ = v___x_237_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_234_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_234_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
else
{
lean_object* v_e_x27_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_279_; 
lean_del_object(v___x_221_);
lean_dec_ref(v_e_156_);
v_e_x27_253_ = lean_ctor_get(v_a_219_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_279_ == 0)
{
v___x_255_ = v_a_219_;
v_isShared_256_ = v_isSharedCheck_279_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_e_x27_253_);
lean_dec(v_a_219_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_279_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
uint8_t v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_257_ = 0;
v___x_258_ = 1;
v___x_259_ = l_Lean_Meta_mkLetFVars(v_fvars_157_, v_e_x27_253_, v___x_257_, v___x_257_, v___x_258_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec_ref(v_fvars_157_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_270_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_270_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v_a_260_);
v___x_265_ = v___x_255_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_269_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_267_; 
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_257_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_278_; 
lean_del_object(v___x_255_);
v_a_271_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_278_ == 0)
{
v___x_273_ = v___x_259_;
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_259_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_278_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_274_ == 0)
{
v___x_276_ = v___x_273_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_fvars_157_);
lean_dec_ref(v_e_156_);
return v___x_218_;
}
}
else
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
lean_dec_ref(v_fvars_157_);
lean_dec_ref(v_e_156_);
v_a_281_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_216_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_216_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(lean_object* v_fvars_289_, lean_object* v_body_290_, uint8_t v_modified_291_, lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_array_push(v_fvars_289_, v_x_292_);
v___x_304_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_body_290_, v___x_303_, v_modified_291_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(lean_object* v_e_305_, lean_object* v_fvars_306_, lean_object* v_modified_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
uint8_t v_modified_boxed_318_; lean_object* v_res_319_; 
v_modified_boxed_318_ = lean_unbox(v_modified_307_);
v_res_319_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_305_, v_fvars_306_, v_modified_boxed_318_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec(v_a_309_);
lean_dec(v_a_308_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet(lean_object* v_e_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; 
v___x_333_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0));
v___x_334_ = 0;
v___x_335_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(v_e_322_, v___x_333_, v___x_334_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_Sym_DSimp_dsimpLet(v_e_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec(v_a_338_);
lean_dec(v_a_337_);
return v_res_347_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Let(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Let(builtin);
}
#ifdef __cplusplus
}
#endif
