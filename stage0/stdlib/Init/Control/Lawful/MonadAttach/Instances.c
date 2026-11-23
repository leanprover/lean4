// Lean compiler output
// Module: Init.Control.Lawful.MonadAttach.Instances
// Imports: import Init.Control.Lawful.MonadAttach.Lemmas public import Init.Control.Lawful.Basic public import Init.Control.State public import Init.Control.StateRef public import Init.Control.EState public import Init.Ext
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
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__Except_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__Except_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_instMonadAttach_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_instMonadAttach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__Except_map_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref_known(v_x_1_, 1);
v___x_5_ = lean_apply_1(v_h__1_2_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_a_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref_known(v_x_1_, 1);
v___x_7_ = lean_apply_1(v_h__2_3_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__Except_map_match__1_splitter(lean_object* v_00_u03b5_8_, lean_object* v_00_u03b1_9_, lean_object* v_motive_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_13_);
v_a_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v_x_11_, 1);
v___x_15_ = lean_apply_1(v_h__1_12_, v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_12_);
v_a_16_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v_x_11_, 1);
v___x_17_ = lean_apply_1(v_h__2_13_, v_a_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(lean_object* v_a_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_){
_start:
{
if (lean_obj_tag(v_a_18_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_19_);
v_a_21_ = lean_ctor_get(v_a_18_, 0);
lean_inc(v_a_21_);
lean_dec_ref_known(v_a_18_, 1);
v___x_22_ = lean_apply_2(v_h__2_20_, v_a_21_, lean_box(0));
return v___x_22_;
}
else
{
lean_object* v_a_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_20_);
v_a_23_ = lean_ctor_get(v_a_18_, 0);
lean_inc(v_a_23_);
lean_dec_ref_known(v_a_18_, 1);
v___x_24_ = lean_apply_2(v_h__1_19_, v_a_23_, lean_box(0));
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(lean_object* v_m_25_, lean_object* v_00_u03b5_26_, lean_object* v_inst_27_, lean_object* v_00_u03b1_28_, lean_object* v_x_29_, lean_object* v_motive_30_, lean_object* v_a_31_, lean_object* v_h_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
if (lean_obj_tag(v_a_31_) == 0)
{
lean_object* v_a_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_33_);
v_a_35_ = lean_ctor_get(v_a_31_, 0);
lean_inc(v_a_35_);
lean_dec_ref_known(v_a_31_, 1);
v___x_36_ = lean_apply_2(v_h__2_34_, v_a_35_, lean_box(0));
return v___x_36_;
}
else
{
lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_34_);
v_a_37_ = lean_ctor_get(v_a_31_, 0);
lean_inc(v_a_37_);
lean_dec_ref_known(v_a_31_, 1);
v___x_38_ = lean_apply_2(v_h__1_33_, v_a_37_, lean_box(0));
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(lean_object* v_m_39_, lean_object* v_00_u03b5_40_, lean_object* v_inst_41_, lean_object* v_00_u03b1_42_, lean_object* v_x_43_, lean_object* v_motive_44_, lean_object* v_a_45_, lean_object* v_h_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(v_m_39_, v_00_u03b5_40_, v_inst_41_, v_00_u03b1_42_, v_x_43_, v_motive_44_, v_a_45_, v_h_46_, v_h__1_47_, v_h__2_48_);
lean_dec(v_x_43_);
lean_dec(v_inst_41_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_51_);
v_a_53_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_a_53_);
lean_dec_ref_known(v_x_50_, 1);
v___x_54_ = lean_apply_1(v_h__2_52_, v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_52_);
v_a_55_ = lean_ctor_get(v_x_50_, 0);
lean_inc(v_a_55_);
lean_dec_ref_known(v_x_50_, 1);
v___x_56_ = lean_apply_1(v_h__1_51_, v_a_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_57_, lean_object* v_00_u03b1_58_, lean_object* v_motive_59_, lean_object* v_x_60_, lean_object* v_h__1_61_, lean_object* v_h__2_62_){
_start:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_64_; 
lean_dec(v_h__1_61_);
v_a_63_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v_x_60_, 1);
v___x_64_ = lean_apply_1(v_h__2_62_, v_a_63_);
return v___x_64_;
}
else
{
lean_object* v_a_65_; lean_object* v___x_66_; 
lean_dec(v_h__2_62_);
v_a_65_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v_x_60_, 1);
v___x_66_ = lean_apply_1(v_h__1_61_, v_a_65_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(lean_object* v_a_67_, lean_object* v_h__1_68_, lean_object* v_h__2_69_){
_start:
{
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_68_);
v_a_70_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v_a_67_, 1);
v___x_71_ = lean_apply_1(v_h__2_69_, v_a_70_);
return v___x_71_;
}
else
{
lean_object* v_a_72_; lean_object* v___x_73_; 
lean_dec(v_h__2_69_);
v_a_72_ = lean_ctor_get(v_a_67_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v_a_67_, 1);
v___x_73_ = lean_apply_1(v_h__1_68_, v_a_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(lean_object* v_00_u03b5_74_, lean_object* v_00_u03b1_75_, lean_object* v_P_76_, lean_object* v_motive_77_, lean_object* v_a_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_){
_start:
{
if (lean_obj_tag(v_a_78_) == 0)
{
lean_object* v_a_81_; lean_object* v___x_82_; 
lean_dec(v_h__1_79_);
v_a_81_ = lean_ctor_get(v_a_78_, 0);
lean_inc(v_a_81_);
lean_dec_ref_known(v_a_78_, 1);
v___x_82_ = lean_apply_1(v_h__2_80_, v_a_81_);
return v___x_82_;
}
else
{
lean_object* v_a_83_; lean_object* v___x_84_; 
lean_dec(v_h__2_80_);
v_a_83_ = lean_ctor_get(v_a_78_, 0);
lean_inc(v_a_83_);
lean_dec_ref_known(v_a_78_, 1);
v___x_84_ = lean_apply_1(v_h__1_79_, v_a_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_instMonadAttach_match__1_splitter___redArg(lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v_a_88_; lean_object* v_a_89_; lean_object* v___x_90_; 
lean_dec(v_h__2_87_);
v_a_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_a_88_);
v_a_89_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_a_89_);
lean_dec_ref_known(v_x_85_, 2);
v___x_90_ = lean_apply_3(v_h__1_86_, v_a_88_, v_a_89_, lean_box(0));
return v___x_90_;
}
else
{
lean_object* v_a_91_; lean_object* v_a_92_; lean_object* v___x_93_; 
lean_dec(v_h__1_86_);
v_a_91_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_a_91_);
v_a_92_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_a_92_);
lean_dec_ref_known(v_x_85_, 2);
v___x_93_ = lean_apply_3(v_h__2_87_, v_a_91_, v_a_92_, lean_box(0));
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_instMonadAttach_match__1_splitter(lean_object* v_00_u03b5_94_, lean_object* v_00_u03c3_95_, lean_object* v_00_u03b1_96_, lean_object* v_motive_97_, lean_object* v_x_98_, lean_object* v_h__1_99_, lean_object* v_h__2_100_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v_a_101_; lean_object* v_a_102_; lean_object* v___x_103_; 
lean_dec(v_h__2_100_);
v_a_101_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_a_101_);
v_a_102_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_a_102_);
lean_dec_ref_known(v_x_98_, 2);
v___x_103_ = lean_apply_3(v_h__1_99_, v_a_101_, v_a_102_, lean_box(0));
return v___x_103_;
}
else
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_106_; 
lean_dec(v_h__1_99_);
v_a_104_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_a_104_);
v_a_105_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_a_105_);
lean_dec_ref_known(v_x_98_, 2);
v___x_106_ = lean_apply_3(v_h__2_100_, v_a_104_, v_a_105_, lean_box(0));
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_bind_match__1_splitter___redArg(lean_object* v_x_107_, lean_object* v_h__1_108_, lean_object* v_h__2_109_){
_start:
{
if (lean_obj_tag(v_x_107_) == 0)
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_112_; 
lean_dec(v_h__2_109_);
v_a_110_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_a_110_);
v_a_111_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_a_111_);
lean_dec_ref_known(v_x_107_, 2);
v___x_112_ = lean_apply_2(v_h__1_108_, v_a_110_, v_a_111_);
return v___x_112_;
}
else
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_115_; 
lean_dec(v_h__1_108_);
v_a_113_ = lean_ctor_get(v_x_107_, 0);
lean_inc(v_a_113_);
v_a_114_ = lean_ctor_get(v_x_107_, 1);
lean_inc(v_a_114_);
lean_dec_ref_known(v_x_107_, 2);
v___x_115_ = lean_apply_2(v_h__2_109_, v_a_113_, v_a_114_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__EStateM_bind_match__1_splitter(lean_object* v_00_u03b5_116_, lean_object* v_00_u03c3_117_, lean_object* v_00_u03b1_118_, lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_h__2_122_);
v_a_123_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_123_);
v_a_124_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_a_124_);
lean_dec_ref_known(v_x_120_, 2);
v___x_125_ = lean_apply_2(v_h__1_121_, v_a_123_, v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_a_126_; lean_object* v_a_127_; lean_object* v___x_128_; 
lean_dec(v_h__1_121_);
v_a_126_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_126_);
v_a_127_ = lean_ctor_get(v_x_120_, 1);
lean_inc(v_a_127_);
lean_dec_ref_known(v_x_120_, 2);
v___x_128_ = lean_apply_2(v_h__2_122_, v_a_126_, v_a_127_);
return v___x_128_;
}
}
}
lean_object* runtime_initialize_Init_Control_Lawful_MonadAttach_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_EState(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Lawful_MonadAttach_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Control_Lawful_MonadAttach_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Lawful_MonadAttach_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Lawful_MonadAttach_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* initialize_Init_Control_EState(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Lawful_MonadAttach_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Lawful_MonadAttach_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_EState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Lawful_MonadAttach_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
