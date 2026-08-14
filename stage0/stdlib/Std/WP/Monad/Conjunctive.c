// Lean compiler output
// Module: Std.WP.Monad.Conjunctive
// Imports: public import Std.WP.Conjunctive public import Std.WP.Monad.Instances
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
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EStateM_wpInst_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_4_; lean_object* v_a_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_3_);
v_a_4_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_4_);
v_a_5_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_5_);
lean_dec_ref_known(v_x_1_, 2);
v___x_6_ = lean_apply_2(v_h__1_2_, v_a_4_, v_a_5_);
return v___x_6_;
}
else
{
lean_object* v_a_7_; lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__1_2_);
v_a_7_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_a_7_);
v_a_8_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_a_8_);
lean_dec_ref_known(v_x_1_, 2);
v___x_9_ = lean_apply_2(v_h__2_3_, v_a_7_, v_a_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EStateM_wpInst_match__1_splitter(lean_object* v_00_u03b5_10_, lean_object* v_00_u03c3_11_, lean_object* v_00_u03b1_12_, lean_object* v_motive_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v_a_17_; lean_object* v_a_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_16_);
v_a_17_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_17_);
v_a_18_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_a_18_);
lean_dec_ref_known(v_x_14_, 2);
v___x_19_ = lean_apply_2(v_h__1_15_, v_a_17_, v_a_18_);
return v___x_19_;
}
else
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; 
lean_dec(v_h__1_15_);
v_a_20_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v_x_14_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v_x_14_, 2);
v___x_22_ = lean_apply_2(v_h__2_16_, v_a_20_, v_a_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushOption_match__1_splitter___redArg(lean_object* v_x_23_, lean_object* v_h__1_24_, lean_object* v_h__2_25_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v_h__1_24_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_apply_1(v_h__2_25_, v___x_26_);
return v___x_27_;
}
else
{
lean_object* v_val_28_; lean_object* v___x_29_; 
lean_dec(v_h__2_25_);
v_val_28_ = lean_ctor_get(v_x_23_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v_x_23_, 1);
v___x_29_ = lean_apply_1(v_h__1_24_, v_val_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushOption_match__1_splitter(lean_object* v_00_u03b1_30_, lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_){
_start:
{
if (lean_obj_tag(v_x_32_) == 0)
{
lean_object* v___x_35_; lean_object* v___x_36_; 
lean_dec(v_h__1_33_);
v___x_35_ = lean_box(0);
v___x_36_ = lean_apply_1(v_h__2_34_, v___x_35_);
return v___x_36_;
}
else
{
lean_object* v_val_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_34_);
v_val_37_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v_x_32_, 1);
v___x_38_ = lean_apply_1(v_h__1_33_, v_val_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_43_; 
lean_dec(v_h__1_40_);
v_a_42_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_a_42_);
lean_dec_ref_known(v_x_39_, 1);
v___x_43_ = lean_apply_1(v_h__2_41_, v_a_42_);
return v___x_43_;
}
else
{
lean_object* v_a_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_41_);
v_a_44_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v_x_39_, 1);
v___x_45_ = lean_apply_1(v_h__1_40_, v_a_44_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_WP_Monad_Conjunctive_0__Std_WP_EPost_Cons_pushExcept_match__1_splitter(lean_object* v_00_u03b1_46_, lean_object* v_00_u03b5_47_, lean_object* v_motive_48_, lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_50_);
v_a_52_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_a_52_);
lean_dec_ref_known(v_x_49_, 1);
v___x_53_ = lean_apply_1(v_h__2_51_, v_a_52_);
return v___x_53_;
}
else
{
lean_object* v_a_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_51_);
v_a_54_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_a_54_);
lean_dec_ref_known(v_x_49_, 1);
v___x_55_ = lean_apply_1(v_h__1_50_, v_a_54_);
return v___x_55_;
}
}
}
lean_object* runtime_initialize_Std_WP_Conjunctive(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Monad_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_WP_Monad_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_WP_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Monad_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_WP_Monad_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_WP_Conjunctive(uint8_t builtin);
lean_object* initialize_Std_WP_Monad_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_WP_Monad_Conjunctive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_WP_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Monad_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Monad_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_WP_Monad_Conjunctive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_WP_Monad_Conjunctive(builtin);
}
#ifdef __cplusplus
}
#endif
