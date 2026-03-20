// Lean compiler output
// Module: Init.Control.Do
// Imports: public import Init.Control.Except public import Init.Control.Option
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
LEAN_EXPORT lean_object* l_EarlyReturnT_return___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EarlyReturnT_return(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EarlyReturn_runK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EarlyReturn_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BreakT_break___redArg(lean_object*);
LEAN_EXPORT lean_object* l_BreakT_break(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Break_runK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Break_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ContinueT_continue___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ContinueT_continue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Continue_runK___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Continue_runK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_EarlyReturnT_return___redArg(lean_object* v_inst_1_, lean_object* v_r_2_){
_start:
{
lean_object* v_toApplicative_3_; lean_object* v_toPure_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v_toApplicative_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc_ref(v_toApplicative_3_);
lean_dec_ref(v_inst_1_);
v_toPure_4_ = lean_ctor_get(v_toApplicative_3_, 1);
lean_inc(v_toPure_4_);
lean_dec_ref(v_toApplicative_3_);
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_r_2_);
v___x_6_ = lean_apply_2(v_toPure_4_, lean_box(0), v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_EarlyReturnT_return(lean_object* v_00_u03c1_7_, lean_object* v_m_8_, lean_object* v_00_u03b1_9_, lean_object* v_inst_10_, lean_object* v_r_11_){
_start:
{
lean_object* v_toApplicative_12_; lean_object* v_toPure_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_toApplicative_12_ = lean_ctor_get(v_inst_10_, 0);
lean_inc_ref(v_toApplicative_12_);
lean_dec_ref(v_inst_10_);
v_toPure_13_ = lean_ctor_get(v_toApplicative_12_, 1);
lean_inc(v_toPure_13_);
lean_dec_ref(v_toApplicative_12_);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v_r_11_);
v___x_15_ = lean_apply_2(v_toPure_13_, lean_box(0), v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_EarlyReturn_runK___redArg(lean_object* v_x_16_, lean_object* v_ret_17_, lean_object* v_pure_18_){
_start:
{
if (lean_obj_tag(v_x_16_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_20_; 
lean_dec(v_pure_18_);
v_a_19_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_a_19_);
lean_dec_ref(v_x_16_);
v___x_20_ = lean_apply_1(v_ret_17_, v_a_19_);
return v___x_20_;
}
else
{
lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_ret_17_);
v_a_21_ = lean_ctor_get(v_x_16_, 0);
lean_inc(v_a_21_);
lean_dec_ref(v_x_16_);
v___x_22_ = lean_apply_1(v_pure_18_, v_a_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_EarlyReturn_runK(lean_object* v_00_u03c1_23_, lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_x_26_, lean_object* v_ret_27_, lean_object* v_pure_28_){
_start:
{
if (lean_obj_tag(v_x_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_pure_28_);
v_a_29_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v_x_26_);
v___x_30_ = lean_apply_1(v_ret_27_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_ret_27_);
v_a_31_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_x_26_);
v___x_32_ = lean_apply_1(v_pure_28_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_BreakT_break___redArg(lean_object* v_inst_33_){
_start:
{
lean_object* v_toApplicative_34_; lean_object* v_toPure_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v_toApplicative_34_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_34_);
lean_dec_ref(v_inst_33_);
v_toPure_35_ = lean_ctor_get(v_toApplicative_34_, 1);
lean_inc(v_toPure_35_);
lean_dec_ref(v_toApplicative_34_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_2(v_toPure_35_, lean_box(0), v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_BreakT_break(lean_object* v_00_u03b1_38_, lean_object* v_m_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v_toApplicative_41_; lean_object* v_toPure_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_toApplicative_41_ = lean_ctor_get(v_inst_40_, 0);
lean_inc_ref(v_toApplicative_41_);
lean_dec_ref(v_inst_40_);
v_toPure_42_ = lean_ctor_get(v_toApplicative_41_, 1);
lean_inc(v_toPure_42_);
lean_dec_ref(v_toApplicative_41_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_2(v_toPure_42_, lean_box(0), v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Break_runK___redArg(lean_object* v_x_45_, lean_object* v_breakK_46_, lean_object* v_successK_47_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_successK_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_breakK_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_breakK_46_);
v_val_50_ = lean_ctor_get(v_x_45_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v_x_45_);
v___x_51_ = lean_apply_1(v_successK_47_, v_val_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Break_runK(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_x_54_, lean_object* v_breakK_55_, lean_object* v_successK_56_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; 
lean_dec(v_successK_56_);
v___x_57_ = lean_box(0);
v___x_58_ = lean_apply_1(v_breakK_55_, v___x_57_);
return v___x_58_;
}
else
{
lean_object* v_val_59_; lean_object* v___x_60_; 
lean_dec(v_breakK_55_);
v_val_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_val_59_);
lean_dec_ref(v_x_54_);
v___x_60_ = lean_apply_1(v_successK_56_, v_val_59_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_ContinueT_continue___redArg(lean_object* v_inst_61_){
_start:
{
lean_object* v_toApplicative_62_; lean_object* v_toPure_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_toApplicative_62_ = lean_ctor_get(v_inst_61_, 0);
lean_inc_ref(v_toApplicative_62_);
lean_dec_ref(v_inst_61_);
v_toPure_63_ = lean_ctor_get(v_toApplicative_62_, 1);
lean_inc(v_toPure_63_);
lean_dec_ref(v_toApplicative_62_);
v___x_64_ = lean_box(0);
v___x_65_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_ContinueT_continue(lean_object* v_00_u03b1_66_, lean_object* v_m_67_, lean_object* v_inst_68_){
_start:
{
lean_object* v_toApplicative_69_; lean_object* v_toPure_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_toApplicative_69_ = lean_ctor_get(v_inst_68_, 0);
lean_inc_ref(v_toApplicative_69_);
lean_dec_ref(v_inst_68_);
v_toPure_70_ = lean_ctor_get(v_toApplicative_69_, 1);
lean_inc(v_toPure_70_);
lean_dec_ref(v_toApplicative_69_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_apply_2(v_toPure_70_, lean_box(0), v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Continue_runK___redArg(lean_object* v_x_73_, lean_object* v_continueK_74_, lean_object* v_successK_75_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_successK_75_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_apply_1(v_continueK_74_, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v_a_78_; lean_object* v___x_79_; 
lean_dec(v_continueK_74_);
v_a_78_ = lean_ctor_get(v_x_73_, 0);
lean_inc(v_a_78_);
lean_dec_ref(v_x_73_);
v___x_79_ = lean_apply_1(v_successK_75_, v_a_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Continue_runK(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_x_82_, lean_object* v_continueK_83_, lean_object* v_successK_84_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_successK_84_);
v___x_85_ = lean_box(0);
v___x_86_ = lean_apply_1(v_continueK_83_, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_a_87_; lean_object* v___x_88_; 
lean_dec(v_continueK_83_);
v_a_87_ = lean_ctor_get(v_x_82_, 0);
lean_inc(v_a_87_);
lean_dec_ref(v_x_82_);
v___x_88_ = lean_apply_1(v_successK_84_, v_a_87_);
return v___x_88_;
}
}
}
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Option(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Do(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Do(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_Control_Option(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Do(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Option(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Do(builtin);
}
#ifdef __cplusplus
}
#endif
