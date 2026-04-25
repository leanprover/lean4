// Lean compiler output
// Module: Init.Control.Lawful.MonadLift.Instances
// Imports: import all Init.Control.Option import all Init.Control.Except public import Init.Control.ExceptCps import all Init.Control.ExceptCps import all Init.Control.StateRef public import Init.Control.StateCps import all Init.Control.StateCps import all Init.Control.Id public import Init.Control.Lawful.MonadLift.Basic public import Init.Control.Option public import Init.Control.State public import Init.Control.StateRef import Init.Control.Lawful.Instances import Init.Control.Lawful.MonadLift.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter___redArg(lean_object* v_____do__lift_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_____do__lift_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_val_6_ = lean_ctor_get(v_____do__lift_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_____do__lift_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__OptionT_bind_match__1_splitter(lean_object* v_00_u03b1_8_, lean_object* v_motive_9_, lean_object* v_____do__lift_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_____do__lift_10_) == 0)
{
lean_object* v___x_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v___x_13_ = lean_box(0);
v___x_14_ = lean_apply_1(v_h__2_12_, v___x_13_);
return v___x_14_;
}
else
{
lean_object* v_val_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_val_15_ = lean_ctor_get(v_____do__lift_10_, 0);
lean_inc(v_val_15_);
lean_dec_ref(v_____do__lift_10_);
v___x_16_ = lean_apply_1(v_h__1_11_, v_val_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter___redArg(lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_19_);
v_a_20_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_x_17_);
v___x_21_ = lean_apply_1(v_h__1_18_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__1_18_);
v_a_22_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v_x_17_);
v___x_23_ = lean_apply_1(v_h__2_19_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__Except_map_match__1_splitter(lean_object* v_00_u03b5_24_, lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; 
lean_dec(v_h__2_29_);
v_a_30_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_a_30_);
lean_dec_ref(v_x_27_);
v___x_31_ = lean_apply_1(v_h__1_28_, v_a_30_);
return v___x_31_;
}
else
{
lean_object* v_a_32_; lean_object* v___x_33_; 
lean_dec(v_h__1_28_);
v_a_32_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_a_32_);
lean_dec_ref(v_x_27_);
v___x_33_ = lean_apply_1(v_h__2_29_, v_a_32_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter___redArg(lean_object* v_x_34_, lean_object* v_h__1_35_, lean_object* v_h__2_36_){
_start:
{
if (lean_obj_tag(v_x_34_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_35_);
v_a_37_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_37_);
lean_dec_ref(v_x_34_);
v___x_38_ = lean_apply_1(v_h__2_36_, v_a_37_);
return v___x_38_;
}
else
{
lean_object* v_a_39_; lean_object* v___x_40_; 
lean_dec(v_h__2_36_);
v_a_39_ = lean_ctor_get(v_x_34_, 0);
lean_inc(v_a_39_);
lean_dec_ref(v_x_34_);
v___x_40_ = lean_apply_1(v_h__1_35_, v_a_39_);
return v___x_40_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Control_Lawful_MonadLift_Instances_0__ExceptT_bindCont_match__1_splitter(lean_object* v_00_u03b5_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_x_44_, lean_object* v_h__1_45_, lean_object* v_h__2_46_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_45_);
v_a_47_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_47_);
lean_dec_ref(v_x_44_);
v___x_48_ = lean_apply_1(v_h__2_46_, v_a_47_);
return v___x_48_;
}
else
{
lean_object* v_a_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_46_);
v_a_49_ = lean_ctor_get(v_x_44_, 0);
lean_inc(v_a_49_);
lean_dec_ref(v_x_44_);
v___x_50_ = lean_apply_1(v_h__1_45_, v_a_49_);
return v___x_50_;
}
}
}
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_ExceptCps(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_ExceptCps(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateCps(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateCps(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Id(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_MonadLift_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Lawful_MonadLift_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Lawful_MonadLift_Instances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_Control_ExceptCps(uint8_t builtin);
lean_object* initialize_Init_Control_ExceptCps(uint8_t builtin);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* initialize_Init_Control_StateCps(uint8_t builtin);
lean_object* initialize_Init_Control_StateCps(uint8_t builtin);
lean_object* initialize_Init_Control_Id(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_MonadLift_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
lean_object* initialize_Init_Control_StateRef(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_Instances(uint8_t builtin);
lean_object* initialize_Init_Control_Lawful_MonadLift_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Lawful_MonadLift_Instances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_ExceptCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateCps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Id(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_MonadLift_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_StateRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Lawful_MonadLift_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Lawful_MonadLift_Instances(builtin);
}
#ifdef __cplusplus
}
#endif
