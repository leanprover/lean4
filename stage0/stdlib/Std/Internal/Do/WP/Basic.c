// Lean compiler output
// Module: Std.Internal.Do.WP.Basic
// Imports: public import Std.Internal.Do.PredTrans
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
lean_object* l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Do_pushArg___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_WP_wp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_WP_wp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Id_wpInst(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Id_instWPMonad;
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Option_wpInst(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Option_instWPMonad;
LEAN_EXPORT lean_object* l_Std_Internal_Do_Except_wpInst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_Except_instWPMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EStateM_wpInst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_EStateM_instWPMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Do_WP_wp___redArg(lean_object* v_self_1_, lean_object* v_x_2_, lean_object* v_post_3_, lean_object* v_epost_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_3(v_self_1_, v_x_2_, v_post_3_, v_epost_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_WP_wp(lean_object* v_Prog_6_, lean_object* v_Value_7_, lean_object* v_Pred_8_, lean_object* v_EPred_9_, lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_self_12_, lean_object* v_x_13_, lean_object* v_post_14_, lean_object* v_epost_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_3(v_self_12_, v_x_13_, v_post_14_, v_epost_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad___redArg(lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_apply_1(v_inst_17_, lean_box(0));
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad(lean_object* v_m_19_, lean_object* v_Pred_20_, lean_object* v_EPred_21_, lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_inst_25_, lean_object* v_inst_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_1(v_inst_26_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_instWPOfWPMonad___boxed(lean_object* v_m_28_, lean_object* v_Pred_29_, lean_object* v_EPred_30_, lean_object* v_00_u03b1_31_, lean_object* v_inst_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Internal_Do_instWPOfWPMonad(v_m_28_, v_Pred_29_, v_EPred_30_, v_00_u03b1_31_, v_inst_32_, v_inst_33_, v_inst_34_, v_inst_35_);
lean_dec_ref(v_inst_32_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Id_wpInst(lean_object* v_00_u03b1_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
static lean_object* _init_l_Std_Internal_Do_Id_instWPMonad(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_box(0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst___redArg___lam__0(lean_object* v_inst_40_, lean_object* v_x_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_apply_1(v_inst_40_, v_x_41_);
v___x_45_ = l_Std_Internal_Do_PredTrans_pushExcept___redArg___lam__1(v___x_44_, v___y_42_, v___y_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst___redArg(lean_object* v_inst_46_){
_start:
{
lean_object* v___f_47_; 
v___f_47_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ExceptT_wpInst___redArg___lam__0), 4, 1);
lean_closure_set(v___f_47_, 0, v_inst_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_wpInst(lean_object* v_m_48_, lean_object* v_EPred_49_, lean_object* v_00_u03b5_50_, lean_object* v_00_u03b1_51_, lean_object* v_Pred_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ExceptT_wpInst___redArg___lam__0), 4, 1);
lean_closure_set(v___f_56_, 0, v_inst_55_);
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0(lean_object* v_inst_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_apply_1(v_inst_57_, lean_box(0));
v___x_63_ = l_Std_Internal_Do_ExceptT_wpInst___redArg___lam__0(v___x_62_, v___y_59_, v___y_60_, v___y_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___redArg(lean_object* v_inst_64_){
_start:
{
lean_object* v___f_65_; 
v___f_65_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_65_, 0, v_inst_64_);
return v___f_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad(lean_object* v_m_66_, lean_object* v_EPred_67_, lean_object* v_00_u03b5_68_, lean_object* v_Pred_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ExceptT_instWPMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_74_, 0, v_inst_73_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ExceptT_instWPMonad___boxed(lean_object* v_m_75_, lean_object* v_EPred_76_, lean_object* v_00_u03b5_77_, lean_object* v_Pred_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Std_Internal_Do_ExceptT_instWPMonad(v_m_75_, v_EPred_76_, v_00_u03b5_77_, v_Pred_78_, v_inst_79_, v_inst_80_, v_inst_81_, v_inst_82_);
lean_dec_ref(v_inst_79_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst___redArg___lam__0(lean_object* v_inst_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_apply_1(v_inst_84_, v_x_85_);
v___x_89_ = l_Std_Internal_Do_PredTrans_pushOption___redArg___lam__1(v___x_88_, v___y_86_, v___y_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst___redArg(lean_object* v_inst_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = lean_alloc_closure((void*)(l_Std_Internal_Do_OptionT_wpInst___redArg___lam__0), 4, 1);
lean_closure_set(v___f_91_, 0, v_inst_90_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_wpInst(lean_object* v_m_92_, lean_object* v_EPred_93_, lean_object* v_00_u03b1_94_, lean_object* v_Pred_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v___f_99_; 
v___f_99_ = lean_alloc_closure((void*)(l_Std_Internal_Do_OptionT_wpInst___redArg___lam__0), 4, 1);
lean_closure_set(v___f_99_, 0, v_inst_98_);
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0(lean_object* v_inst_100_, lean_object* v_x_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_apply_1(v_inst_100_, lean_box(0));
v___x_106_ = l_Std_Internal_Do_OptionT_wpInst___redArg___lam__0(v___x_105_, v___y_102_, v___y_103_, v___y_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___redArg(lean_object* v_inst_107_){
_start:
{
lean_object* v___f_108_; 
v___f_108_ = lean_alloc_closure((void*)(l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_108_, 0, v_inst_107_);
return v___f_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad(lean_object* v_m_109_, lean_object* v_EPred_110_, lean_object* v_Pred_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = lean_alloc_closure((void*)(l_Std_Internal_Do_OptionT_instWPMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_116_, 0, v_inst_115_);
return v___f_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_OptionT_instWPMonad___boxed(lean_object* v_m_117_, lean_object* v_EPred_118_, lean_object* v_Pred_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_inst_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Internal_Do_OptionT_instWPMonad(v_m_117_, v_EPred_118_, v_Pred_119_, v_inst_120_, v_inst_121_, v_inst_122_, v_inst_123_);
lean_dec_ref(v_inst_120_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg___lam__0(lean_object* v_x_125_, lean_object* v_inst_126_, lean_object* v_x_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_apply_1(v_x_125_, v_x_127_);
v___x_131_ = lean_apply_3(v_inst_126_, v___x_130_, v___y_128_, v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg___lam__1(lean_object* v_inst_132_, lean_object* v_x_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___x_138_; 
v___f_137_ = lean_alloc_closure((void*)(l_Std_Internal_Do_StateT_wpInst___redArg___lam__0), 5, 2);
lean_closure_set(v___f_137_, 0, v_x_133_);
lean_closure_set(v___f_137_, 1, v_inst_132_);
v___x_138_ = l_Std_Internal_Do_pushArg___redArg___lam__1(v___f_137_, v___y_134_, v___y_135_, v___y_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst___redArg(lean_object* v_inst_139_){
_start:
{
lean_object* v___f_140_; 
v___f_140_ = lean_alloc_closure((void*)(l_Std_Internal_Do_StateT_wpInst___redArg___lam__1), 5, 1);
lean_closure_set(v___f_140_, 0, v_inst_139_);
return v___f_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_wpInst(lean_object* v_m_141_, lean_object* v_00_u03b1_142_, lean_object* v_EPred_143_, lean_object* v_00_u03c3_144_, lean_object* v_Pred_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_){
_start:
{
lean_object* v___f_149_; 
v___f_149_ = lean_alloc_closure((void*)(l_Std_Internal_Do_StateT_wpInst___redArg___lam__1), 5, 1);
lean_closure_set(v___f_149_, 0, v_inst_148_);
return v___f_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0(lean_object* v_inst_150_, lean_object* v_x_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_apply_1(v_inst_150_, lean_box(0));
v___x_157_ = l_Std_Internal_Do_StateT_wpInst___redArg___lam__1(v___x_156_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___redArg(lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_159_, 0, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad(lean_object* v_m_160_, lean_object* v_EPred_161_, lean_object* v_00_u03c3_162_, lean_object* v_Pred_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v___f_168_; 
v___f_168_ = lean_alloc_closure((void*)(l_Std_Internal_Do_StateT_instWPMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_168_, 0, v_inst_167_);
return v___f_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_StateT_instWPMonad___boxed(lean_object* v_m_169_, lean_object* v_EPred_170_, lean_object* v_00_u03c3_171_, lean_object* v_Pred_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_Internal_Do_StateT_instWPMonad(v_m_169_, v_EPred_170_, v_00_u03c3_171_, v_Pred_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_);
lean_dec_ref(v_inst_173_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__0(lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_apply_2(v___y_178_, v_a_180_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__1(lean_object* v_inst_182_, lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v___y_186_);
v___f_187_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__0), 3, 2);
lean_closure_set(v___f_187_, 0, v___y_184_);
lean_closure_set(v___f_187_, 1, v___y_186_);
v___x_188_ = lean_apply_1(v_x_183_, v___y_186_);
v___x_189_ = lean_apply_3(v_inst_182_, v___x_188_, v___f_187_, v___y_185_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst___redArg(lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__1), 5, 1);
lean_closure_set(v___f_191_, 0, v_inst_190_);
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_wpInst(lean_object* v_m_192_, lean_object* v_EPred_193_, lean_object* v_00_u03b1_194_, lean_object* v_00_u03c1_195_, lean_object* v_Pred_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__1), 5, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0(lean_object* v_inst_201_, lean_object* v_x_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_apply_1(v_inst_201_, lean_box(0));
v___x_208_ = l_Std_Internal_Do_ReaderT_wpInst___redArg___lam__1(v___x_207_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___redArg(lean_object* v_inst_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_210_, 0, v_inst_209_);
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad(lean_object* v_m_211_, lean_object* v_EPred_212_, lean_object* v_00_u03c1_213_, lean_object* v_Pred_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_){
_start:
{
lean_object* v___f_219_; 
v___f_219_ = lean_alloc_closure((void*)(l_Std_Internal_Do_ReaderT_instWPMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_219_, 0, v_inst_218_);
return v___f_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_ReaderT_instWPMonad___boxed(lean_object* v_m_220_, lean_object* v_EPred_221_, lean_object* v_00_u03c1_222_, lean_object* v_Pred_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Internal_Do_ReaderT_instWPMonad(v_m_220_, v_EPred_221_, v_00_u03c1_222_, v_Pred_223_, v_inst_224_, v_inst_225_, v_inst_226_, v_inst_227_);
lean_dec_ref(v_inst_224_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Option_wpInst(lean_object* v_00_u03b1_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
}
static lean_object* _init_l_Std_Internal_Do_Option_instWPMonad(void){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Except_wpInst(lean_object* v_00_u03b5_232_, lean_object* v_00_u03b1_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_box(0);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_Except_instWPMonad(lean_object* v_00_u03b5_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_box(0);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EStateM_wpInst(lean_object* v_00_u03b5_237_, lean_object* v_00_u03c3_238_, lean_object* v_00_u03b1_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_241_, lean_object* v_h__1_242_, lean_object* v_h__2_243_){
_start:
{
if (lean_obj_tag(v_x_241_) == 0)
{
lean_object* v_a_244_; lean_object* v_a_245_; lean_object* v___x_246_; 
lean_dec(v_h__2_243_);
v_a_244_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_a_244_);
v_a_245_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_a_245_);
lean_dec_ref_known(v_x_241_, 2);
v___x_246_ = lean_apply_2(v_h__1_242_, v_a_244_, v_a_245_);
return v___x_246_;
}
else
{
lean_object* v_a_247_; lean_object* v_a_248_; lean_object* v___x_249_; 
lean_dec(v_h__1_242_);
v_a_247_ = lean_ctor_get(v_x_241_, 0);
lean_inc(v_a_247_);
v_a_248_ = lean_ctor_get(v_x_241_, 1);
lean_inc(v_a_248_);
lean_dec_ref_known(v_x_241_, 2);
v___x_249_ = lean_apply_2(v_h__2_243_, v_a_247_, v_a_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__Std_Internal_Do_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_250_, lean_object* v_00_u03c3_251_, lean_object* v_00_u03b1_252_, lean_object* v_motive_253_, lean_object* v_x_254_, lean_object* v_h__1_255_, lean_object* v_h__2_256_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
lean_object* v_a_257_; lean_object* v_a_258_; lean_object* v___x_259_; 
lean_dec(v_h__2_256_);
v_a_257_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_a_257_);
v_a_258_ = lean_ctor_get(v_x_254_, 1);
lean_inc(v_a_258_);
lean_dec_ref_known(v_x_254_, 2);
v___x_259_ = lean_apply_2(v_h__1_255_, v_a_257_, v_a_258_);
return v___x_259_;
}
else
{
lean_object* v_a_260_; lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_h__1_255_);
v_a_260_ = lean_ctor_get(v_x_254_, 0);
lean_inc(v_a_260_);
v_a_261_ = lean_ctor_get(v_x_254_, 1);
lean_inc(v_a_261_);
lean_dec_ref_known(v_x_254_, 2);
v___x_262_ = lean_apply_2(v_h__2_256_, v_a_260_, v_a_261_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter___redArg(lean_object* v_x_263_, lean_object* v_h__1_264_, lean_object* v_h__2_265_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v_a_266_; lean_object* v_a_267_; lean_object* v___x_268_; 
lean_dec(v_h__2_265_);
v_a_266_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_a_266_);
v_a_267_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_a_267_);
lean_dec_ref_known(v_x_263_, 2);
v___x_268_ = lean_apply_2(v_h__1_264_, v_a_266_, v_a_267_);
return v___x_268_;
}
else
{
lean_object* v_a_269_; lean_object* v_a_270_; lean_object* v___x_271_; 
lean_dec(v_h__1_264_);
v_a_269_ = lean_ctor_get(v_x_263_, 0);
lean_inc(v_a_269_);
v_a_270_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_a_270_);
lean_dec_ref_known(v_x_263_, 2);
v___x_271_ = lean_apply_2(v_h__2_265_, v_a_269_, v_a_270_);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Do_WP_Basic_0__EStateM_bind_match__1_splitter(lean_object* v_00_u03b5_272_, lean_object* v_00_u03c3_273_, lean_object* v_00_u03b1_274_, lean_object* v_motive_275_, lean_object* v_x_276_, lean_object* v_h__1_277_, lean_object* v_h__2_278_){
_start:
{
if (lean_obj_tag(v_x_276_) == 0)
{
lean_object* v_a_279_; lean_object* v_a_280_; lean_object* v___x_281_; 
lean_dec(v_h__2_278_);
v_a_279_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_a_279_);
v_a_280_ = lean_ctor_get(v_x_276_, 1);
lean_inc(v_a_280_);
lean_dec_ref_known(v_x_276_, 2);
v___x_281_ = lean_apply_2(v_h__1_277_, v_a_279_, v_a_280_);
return v___x_281_;
}
else
{
lean_object* v_a_282_; lean_object* v_a_283_; lean_object* v___x_284_; 
lean_dec(v_h__1_277_);
v_a_282_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_a_282_);
v_a_283_ = lean_ctor_get(v_x_276_, 1);
lean_inc(v_a_283_);
lean_dec_ref_known(v_x_276_, 2);
v___x_284_ = lean_apply_2(v_h__2_278_, v_a_282_, v_a_283_);
return v___x_284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Do_EStateM_instWPMonad(lean_object* v_00_u03b5_285_, lean_object* v_00_u03c3_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
lean_object* runtime_initialize_Std_Internal_Do_PredTrans(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Do_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Do_Id_instWPMonad = _init_l_Std_Internal_Do_Id_instWPMonad();
l_Std_Internal_Do_Option_instWPMonad = _init_l_Std_Internal_Do_Option_instWPMonad();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Do_PredTrans(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Do_WP_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Do_PredTrans(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Do_WP_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
