// Lean compiler output
// Module: Init.Control.Lawful.MonadAttach.Instances
// Imports: import Init.Control.Lawful.MonadAttach.Lemmas public import Init.Control.Lawful.Basic public import Init.Control.State public import Init.Control.StateRef public import Init.Ext
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
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(lean_object* v_a_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_a_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_a_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref(v_a_1_);
v___x_5_ = lean_apply_2(v_h__2_3_, v_a_4_, lean_box(0));
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_a_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v_a_1_);
v___x_7_ = lean_apply_2(v_h__1_2_, v_a_6_, lean_box(0));
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(lean_object* v_m_8_, lean_object* v_00_u03b5_9_, lean_object* v_inst_10_, lean_object* v_00_u03b1_11_, lean_object* v_x_12_, lean_object* v_motive_13_, lean_object* v_a_14_, lean_object* v_h_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (lean_obj_tag(v_a_14_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_16_);
v_a_18_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_a_18_);
lean_dec_ref(v_a_14_);
v___x_19_ = lean_apply_2(v_h__2_17_, v_a_18_, lean_box(0));
return v___x_19_;
}
else
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_17_);
v_a_20_ = lean_ctor_get(v_a_14_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_a_14_);
v___x_21_ = lean_apply_2(v_h__1_16_, v_a_20_, lean_box(0));
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(lean_object* v_m_22_, lean_object* v_00_u03b5_23_, lean_object* v_inst_24_, lean_object* v_00_u03b1_25_, lean_object* v_x_26_, lean_object* v_motive_27_, lean_object* v_a_28_, lean_object* v_h_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(v_m_22_, v_00_u03b5_23_, v_inst_24_, v_00_u03b1_25_, v_x_26_, v_motive_27_, v_a_28_, v_h_29_, v_h__1_30_, v_h__2_31_);
lean_dec(v_x_26_);
lean_dec(v_inst_24_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_33_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_37_; 
lean_dec(v_h__1_34_);
v_a_36_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_a_36_);
lean_dec_ref(v_x_33_);
v___x_37_ = lean_apply_1(v_h__2_35_, v_a_36_);
return v___x_37_;
}
else
{
lean_object* v_a_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_35_);
v_a_38_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v_x_33_);
v___x_39_ = lean_apply_1(v_h__1_34_, v_a_38_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_40_, lean_object* v_00_u03b1_41_, lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_){
_start:
{
if (lean_obj_tag(v_x_43_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_47_; 
lean_dec(v_h__1_44_);
v_a_46_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_46_);
lean_dec_ref(v_x_43_);
v___x_47_ = lean_apply_1(v_h__2_45_, v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_a_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_45_);
v_a_48_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v_x_43_);
v___x_49_ = lean_apply_1(v_h__1_44_, v_a_48_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(lean_object* v_a_50_, lean_object* v_h__1_51_, lean_object* v_h__2_52_){
_start:
{
if (lean_obj_tag(v_a_50_) == 0)
{
lean_object* v_a_53_; lean_object* v___x_54_; 
lean_dec(v_h__1_51_);
v_a_53_ = lean_ctor_get(v_a_50_, 0);
lean_inc(v_a_53_);
lean_dec_ref(v_a_50_);
v___x_54_ = lean_apply_1(v_h__2_52_, v_a_53_);
return v___x_54_;
}
else
{
lean_object* v_a_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_52_);
v_a_55_ = lean_ctor_get(v_a_50_, 0);
lean_inc(v_a_55_);
lean_dec_ref(v_a_50_);
v___x_56_ = lean_apply_1(v_h__1_51_, v_a_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(lean_object* v_00_u03b5_57_, lean_object* v_00_u03b1_58_, lean_object* v_P_59_, lean_object* v_motive_60_, lean_object* v_a_61_, lean_object* v_h__1_62_, lean_object* v_h__2_63_){
_start:
{
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; 
lean_dec(v_h__1_62_);
v_a_64_ = lean_ctor_get(v_a_61_, 0);
lean_inc(v_a_64_);
lean_dec_ref(v_a_61_);
v___x_65_ = lean_apply_1(v_h__2_63_, v_a_64_);
return v___x_65_;
}
else
{
lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__2_63_);
v_a_66_ = lean_ctor_get(v_a_61_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v_a_61_);
v___x_67_ = lean_apply_1(v_h__1_62_, v_a_66_);
return v___x_67_;
}
}
}
lean_object* runtime_initialize_Init_Control_Lawful_MonadAttach_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Lawful_MonadAttach_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
