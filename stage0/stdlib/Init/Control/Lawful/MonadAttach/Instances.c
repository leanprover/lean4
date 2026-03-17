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
lean_object* v___x_18_; 
v___x_18_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___redArg(v_a_14_, v_h__1_16_, v_h__2_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter___boxed(lean_object* v_m_19_, lean_object* v_00_u03b5_20_, lean_object* v_inst_21_, lean_object* v_00_u03b1_22_, lean_object* v_x_23_, lean_object* v_motive_24_, lean_object* v_a_25_, lean_object* v_h_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instMonadAttachExceptTOfMonad_match__1_splitter(v_m_19_, v_00_u03b5_20_, v_inst_21_, v_00_u03b1_22_, v_x_23_, v_motive_24_, v_a_25_, v_h_26_, v_h__1_27_, v_h__2_28_);
lean_dec(v_x_23_);
lean_dec(v_inst_21_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_31_);
v_a_33_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_33_);
lean_dec_ref(v_x_30_);
v___x_34_ = lean_apply_1(v_h__2_32_, v_a_33_);
return v___x_34_;
}
else
{
lean_object* v_a_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_32_);
v_a_35_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_a_35_);
lean_dec_ref(v_x_30_);
v___x_36_ = lean_apply_1(v_h__1_31_, v_a_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_37_, lean_object* v_00_u03b1_38_, lean_object* v_motive_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(v_x_40_, v_h__1_41_, v_h__2_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(lean_object* v_a_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_a_44_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v_a_47_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v_a_44_);
v___x_48_ = lean_apply_1(v_h__2_46_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_a_49_ = lean_ctor_get(v_a_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_a_44_);
v___x_50_ = lean_apply_1(v_h__1_45_, v_a_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter(lean_object* v_00_u03b5_51_, lean_object* v_00_u03b1_52_, lean_object* v_P_53_, lean_object* v_motive_54_, lean_object* v_a_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l___private_Init_Control_Lawful_MonadAttach_Instances_0__instLawfulMonadAttachExceptTOfLawfulMonad_match__2_splitter___redArg(v_a_55_, v_h__1_56_, v_h__2_57_);
return v___x_58_;
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
