// Lean compiler output
// Module: Init.Repeat
// Imports: public import Init.Internal.Order.Basic import all Init.System.ST
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
LEAN_EXPORT lean_object* l_Lean_Repeat_opaqueLoop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Repeat_opaqueLoop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instCCPONonemptyMonadOfMonadRepeat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instCCPONonemptyMonadOfMonadRepeat(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadRepeat_defaultInstance___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_MonadRepeat_defaultInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_MonadRepeat_defaultInstance___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_MonadRepeat_defaultInstance___closed__0 = (const lean_object*)&l_MonadRepeat_defaultInstance___closed__0_value;
LEAN_EXPORT lean_object* l_MonadRepeat_defaultInstance(lean_object*);
LEAN_EXPORT const lean_object* l_instMonadRepeatId = (const lean_object*)&l_MonadRepeat_defaultInstance___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatReaderT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatReaderT___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatReaderT___closed__0 = (const lean_object*)&l_instMonadRepeatReaderT___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatOption___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatOption___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatOption___closed__0 = (const lean_object*)&l_instMonadRepeatOption___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadRepeatOption = (const lean_object*)&l_instMonadRepeatOption___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatExcept___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatExcept___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatExcept___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatExcept___closed__0 = (const lean_object*)&l_instMonadRepeatExcept___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatExcept(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateT___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatStateT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatStateT___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatStateT___closed__0 = (const lean_object*)&l_instMonadRepeatStateT___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatStateT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___aux__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___aux__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___aux__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatEStateM___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatEStateM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatEStateM___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatEStateM___closed__0 = (const lean_object*)&l_instMonadRepeatEStateM___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatEStateM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EStateM_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EStateM_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatEST___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatEST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatEST___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatEST___closed__0 = (const lean_object*)&l_instMonadRepeatEST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatEST(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EST_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EST_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatST___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatST___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatST___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatST___closed__0 = (const lean_object*)&l_instMonadRepeatST___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatST(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatEIO___aux__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatEIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatEIO___aux__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_instMonadRepeatEIO___closed__0 = (const lean_object*)&l_instMonadRepeatEIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatEIO(lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatBaseIO___aux__1(lean_object*, lean_object*);
static const lean_closure_object l_instMonadRepeatBaseIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadRepeatBaseIO___aux__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadRepeatBaseIO___closed__0 = (const lean_object*)&l_instMonadRepeatBaseIO___closed__0_value;
LEAN_EXPORT const lean_object* l_instMonadRepeatBaseIO = (const lean_object*)&l_instMonadRepeatBaseIO___closed__0_value;
LEAN_EXPORT lean_object* l_instMonadRepeatStateCpsT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatStateCpsT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptCpsT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadRepeatExceptCpsT___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Repeat_opaqueLoop___redArg(lean_object* v_f_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
lean_inc(v_f_1_);
v___x_2_ = l_Lean_Repeat_opaqueLoop___redArg(v_f_1_);
v___x_3_ = lean_apply_1(v_f_1_, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Repeat_opaqueLoop(lean_object* v_00_u03b1_4_, lean_object* v_inst_5_, lean_object* v_f_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Repeat_opaqueLoop___redArg(v_f_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_instCCPONonemptyMonadOfMonadRepeat___redArg(lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_inst_8_, lean_box(0), lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_instCCPONonemptyMonadOfMonadRepeat(lean_object* v_m_10_, lean_object* v_00_u03b1_11_, lean_object* v_h_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_inst_13_, lean_box(0), lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_MonadRepeat_defaultInstance___lam__0(lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_box(0);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_MonadRepeat_defaultInstance(lean_object* v_m_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = ((lean_object*)(l_MonadRepeat_defaultInstance___closed__0));
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT___lam__0(lean_object* v_00_u03b1_22_, lean_object* v_h_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_box(0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT(lean_object* v_m_26_, lean_object* v_00_u03c1_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = ((lean_object*)(l_instMonadRepeatReaderT___closed__0));
return v___f_29_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatReaderT___boxed(lean_object* v_m_30_, lean_object* v_00_u03c1_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_instMonadRepeatReaderT(v_m_30_, v_00_u03c1_31_, v_inst_32_);
lean_dec_ref(v_inst_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___aux__1(lean_object* v_m_34_, lean_object* v_00_u03c9_35_, lean_object* v_00_u03c3_36_, lean_object* v_inst_37_, lean_object* v_00_u03b1_38_, lean_object* v_h_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_box(0);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___aux__1___boxed(lean_object* v_m_41_, lean_object* v_00_u03c9_42_, lean_object* v_00_u03c3_43_, lean_object* v_inst_44_, lean_object* v_00_u03b1_45_, lean_object* v_h_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_instMonadRepeatStateRefT_x27___aux__1(v_m_41_, v_00_u03c9_42_, v_00_u03c3_43_, v_inst_44_, v_00_u03b1_45_, v_h_46_);
lean_dec_ref(v_inst_44_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27___redArg(lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_alloc_closure((void*)(l_instMonadRepeatStateRefT_x27___aux__1___boxed), 6, 4);
lean_closure_set(v___x_49_, 0, lean_box(0));
lean_closure_set(v___x_49_, 1, lean_box(0));
lean_closure_set(v___x_49_, 2, lean_box(0));
lean_closure_set(v___x_49_, 3, v_inst_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateRefT_x27(lean_object* v_m_50_, lean_object* v_00_u03c9_51_, lean_object* v_00_u03c3_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_closure((void*)(l_instMonadRepeatStateRefT_x27___aux__1___boxed), 6, 4);
lean_closure_set(v___x_54_, 0, lean_box(0));
lean_closure_set(v___x_54_, 1, lean_box(0));
lean_closure_set(v___x_54_, 2, lean_box(0));
lean_closure_set(v___x_54_, 3, v_inst_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatOption___lam__0(lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExcept___lam__0(lean_object* v_00_u03b1_60_, lean_object* v_x_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExcept(lean_object* v_00_u03b5_64_){
_start:
{
lean_object* v___f_65_; 
v___f_65_ = ((lean_object*)(l_instMonadRepeatExcept___closed__0));
return v___f_65_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateT___lam__0(lean_object* v_00_u03b1_66_, lean_object* v_h_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_box(0);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateT(lean_object* v_m_70_, lean_object* v_00_u03c3_71_, lean_object* v_inst_72_){
_start:
{
lean_object* v___f_73_; 
v___f_73_ = ((lean_object*)(l_instMonadRepeatStateT___closed__0));
return v___f_73_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateT___boxed(lean_object* v_m_74_, lean_object* v_00_u03c3_75_, lean_object* v_inst_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_instMonadRepeatStateT(v_m_74_, v_00_u03c3_75_, v_inst_76_);
lean_dec_ref(v_inst_76_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___aux__1___redArg(lean_object* v_inst_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_apply_2(v_inst_78_, lean_box(0), lean_box(0));
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___aux__1(lean_object* v_m_80_, lean_object* v_00_u03b5_81_, lean_object* v_inst_82_, lean_object* v_00_u03b1_83_, lean_object* v_h_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_apply_2(v_inst_82_, lean_box(0), lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___redArg___lam__0(lean_object* v_inst_86_, lean_object* v_00_u03b1_87_, lean_object* v_h_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_2(v_inst_86_, lean_box(0), lean_box(0));
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT___redArg(lean_object* v_inst_90_){
_start:
{
lean_object* v___f_91_; 
v___f_91_ = lean_alloc_closure((void*)(l_instMonadRepeatExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_91_, 0, v_inst_90_);
return v___f_91_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptT(lean_object* v_m_92_, lean_object* v_00_u03b5_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v___f_95_; 
v___f_95_ = lean_alloc_closure((void*)(l_instMonadRepeatExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_95_, 0, v_inst_94_);
return v___f_95_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___aux__1___redArg(lean_object* v_inst_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_2(v_inst_96_, lean_box(0), lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___aux__1(lean_object* v_m_98_, lean_object* v_inst_99_, lean_object* v_00_u03b1_100_, lean_object* v_h_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_apply_2(v_inst_99_, lean_box(0), lean_box(0));
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT___redArg(lean_object* v_inst_103_){
_start:
{
lean_object* v___f_104_; 
v___f_104_ = lean_alloc_closure((void*)(l_instMonadRepeatExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_104_, 0, v_inst_103_);
return v___f_104_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatOptionT(lean_object* v_m_105_, lean_object* v_inst_106_){
_start:
{
lean_object* v___f_107_; 
v___f_107_ = lean_alloc_closure((void*)(l_instMonadRepeatExceptT___redArg___lam__0), 3, 1);
lean_closure_set(v___f_107_, 0, v_inst_106_);
return v___f_107_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEStateM___lam__0(lean_object* v_00_u03b1_108_, lean_object* v_h_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEStateM(lean_object* v_00_u03b5_112_, lean_object* v_00_u03c3_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = ((lean_object*)(l_instMonadRepeatEStateM___closed__0));
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EStateM_bind_match__1_splitter___redArg(lean_object* v_x_115_, lean_object* v_h__1_116_, lean_object* v_h__2_117_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v___x_120_; 
lean_dec(v_h__2_117_);
v_a_118_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_118_);
v_a_119_ = lean_ctor_get(v_x_115_, 1);
lean_inc(v_a_119_);
lean_dec_ref(v_x_115_);
v___x_120_ = lean_apply_2(v_h__1_116_, v_a_118_, v_a_119_);
return v___x_120_;
}
else
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_116_);
v_a_121_ = lean_ctor_get(v_x_115_, 0);
lean_inc(v_a_121_);
v_a_122_ = lean_ctor_get(v_x_115_, 1);
lean_inc(v_a_122_);
lean_dec_ref(v_x_115_);
v___x_123_ = lean_apply_2(v_h__2_117_, v_a_121_, v_a_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EStateM_bind_match__1_splitter(lean_object* v_00_u03b5_124_, lean_object* v_00_u03c3_125_, lean_object* v_00_u03b1_126_, lean_object* v_motive_127_, lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v_a_131_; lean_object* v_a_132_; lean_object* v___x_133_; 
lean_dec(v_h__2_130_);
v_a_131_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_a_131_);
v_a_132_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_a_132_);
lean_dec_ref(v_x_128_);
v___x_133_ = lean_apply_2(v_h__1_129_, v_a_131_, v_a_132_);
return v___x_133_;
}
else
{
lean_object* v_a_134_; lean_object* v_a_135_; lean_object* v___x_136_; 
lean_dec(v_h__1_129_);
v_a_134_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_a_134_);
v_a_135_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_a_135_);
lean_dec_ref(v_x_128_);
v___x_136_ = lean_apply_2(v_h__2_130_, v_a_134_, v_a_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEST___lam__0(lean_object* v_00_u03b1_137_, lean_object* v_h_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEST(lean_object* v_00_u03b5_141_, lean_object* v_00_u03c3_142_){
_start:
{
lean_object* v___f_143_; 
v___f_143_ = ((lean_object*)(l_instMonadRepeatEST___closed__0));
return v___f_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EST_bind_match__1_splitter___redArg(lean_object* v_x_144_, lean_object* v_h__1_145_, lean_object* v_h__2_146_){
_start:
{
if (lean_obj_tag(v_x_144_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; 
lean_dec(v_h__2_146_);
v_a_147_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v_x_144_);
v___x_148_ = lean_apply_2(v_h__1_145_, v_a_147_, lean_box(0));
return v___x_148_;
}
else
{
lean_object* v_a_149_; lean_object* v___x_150_; 
lean_dec(v_h__1_145_);
v_a_149_ = lean_ctor_get(v_x_144_, 0);
lean_inc(v_a_149_);
lean_dec_ref(v_x_144_);
v___x_150_ = lean_apply_2(v_h__2_146_, v_a_149_, lean_box(0));
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Repeat_0__EST_bind_match__1_splitter(lean_object* v_00_u03b5_151_, lean_object* v_00_u03c3_152_, lean_object* v_00_u03b1_153_, lean_object* v_motive_154_, lean_object* v_x_155_, lean_object* v_h__1_156_, lean_object* v_h__2_157_){
_start:
{
if (lean_obj_tag(v_x_155_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_157_);
v_a_158_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v_x_155_);
v___x_159_ = lean_apply_2(v_h__1_156_, v_a_158_, lean_box(0));
return v___x_159_;
}
else
{
lean_object* v_a_160_; lean_object* v___x_161_; 
lean_dec(v_h__1_156_);
v_a_160_ = lean_ctor_get(v_x_155_, 0);
lean_inc(v_a_160_);
lean_dec_ref(v_x_155_);
v___x_161_ = lean_apply_2(v_h__2_157_, v_a_160_, lean_box(0));
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatST___lam__0(lean_object* v_00_u03b1_162_, lean_object* v_h_163_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatST(lean_object* v_00_u03c3_166_){
_start:
{
lean_object* v___f_167_; 
v___f_167_ = ((lean_object*)(l_instMonadRepeatST___closed__0));
return v___f_167_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEIO___aux__1(lean_object* v_00_u03b5_168_, lean_object* v_00_u03b1_169_, lean_object* v_h_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatEIO(lean_object* v_00_u03b5_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_instMonadRepeatEIO___closed__0));
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatBaseIO___aux__1(lean_object* v_00_u03b1_175_, lean_object* v_h_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_box(0);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateCpsT(lean_object* v_m_180_, lean_object* v_00_u03c3_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = ((lean_object*)(l_MonadRepeat_defaultInstance___closed__0));
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatStateCpsT___boxed(lean_object* v_m_184_, lean_object* v_00_u03c3_185_, lean_object* v_inst_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_instMonadRepeatStateCpsT(v_m_184_, v_00_u03c3_185_, v_inst_186_);
lean_dec_ref(v_inst_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptCpsT(lean_object* v_m_188_, lean_object* v_00_u03b5_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = ((lean_object*)(l_MonadRepeat_defaultInstance___closed__0));
return v___f_191_;
}
}
LEAN_EXPORT lean_object* l_instMonadRepeatExceptCpsT___boxed(lean_object* v_m_192_, lean_object* v_00_u03b5_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_instMonadRepeatExceptCpsT(v_m_192_, v_00_u03b5_193_, v_inst_194_);
lean_dec_ref(v_inst_194_);
return v_res_195_;
}
}
lean_object* runtime_initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_ST(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin);
lean_object* initialize_Init_System_ST(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Repeat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Internal_Order_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_ST(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Repeat(builtin);
}
#ifdef __cplusplus
}
#endif
