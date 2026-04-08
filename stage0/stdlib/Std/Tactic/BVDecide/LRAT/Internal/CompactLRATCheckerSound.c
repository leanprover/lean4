// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATCheckerSound
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker import Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object* v_step_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_, lean_object* v_h__5_6_){
_start:
{
if (lean_obj_tag(v_step_1_) == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_apply_1(v_h__1_2_, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v_val_9_; 
lean_dec(v_h__1_2_);
v_val_9_ = lean_ctor_get(v_step_1_, 0);
lean_inc(v_val_9_);
lean_dec_ref(v_step_1_);
switch(lean_obj_tag(v_val_9_))
{
case 0:
{
lean_object* v_id_10_; lean_object* v_rupHints_11_; lean_object* v___x_12_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
v_id_10_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_id_10_);
v_rupHints_11_ = lean_ctor_get(v_val_9_, 1);
lean_inc_ref(v_rupHints_11_);
lean_dec_ref(v_val_9_);
v___x_12_ = lean_apply_2(v_h__2_3_, v_id_10_, v_rupHints_11_);
return v___x_12_;
}
case 1:
{
lean_object* v_id_13_; lean_object* v_c_14_; lean_object* v_rupHints_15_; lean_object* v___x_16_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
v_id_13_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_id_13_);
v_c_14_ = lean_ctor_get(v_val_9_, 1);
lean_inc(v_c_14_);
v_rupHints_15_ = lean_ctor_get(v_val_9_, 2);
lean_inc_ref(v_rupHints_15_);
lean_dec_ref(v_val_9_);
v___x_16_ = lean_apply_3(v_h__3_4_, v_id_13_, v_c_14_, v_rupHints_15_);
return v___x_16_;
}
case 2:
{
lean_object* v_id_17_; lean_object* v_c_18_; lean_object* v_pivot_19_; lean_object* v_rupHints_20_; lean_object* v_ratHints_21_; lean_object* v___x_22_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_id_17_ = lean_ctor_get(v_val_9_, 0);
lean_inc(v_id_17_);
v_c_18_ = lean_ctor_get(v_val_9_, 1);
lean_inc(v_c_18_);
v_pivot_19_ = lean_ctor_get(v_val_9_, 2);
lean_inc_ref(v_pivot_19_);
v_rupHints_20_ = lean_ctor_get(v_val_9_, 3);
lean_inc_ref(v_rupHints_20_);
v_ratHints_21_ = lean_ctor_get(v_val_9_, 4);
lean_inc_ref(v_ratHints_21_);
lean_dec_ref(v_val_9_);
v___x_22_ = lean_apply_5(v_h__4_5_, v_id_17_, v_c_18_, v_pivot_19_, v_rupHints_20_, v_ratHints_21_);
return v___x_22_;
}
default: 
{
lean_object* v_ids_23_; lean_object* v___x_24_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_ids_23_ = lean_ctor_get(v_val_9_, 0);
lean_inc_ref(v_ids_23_);
lean_dec_ref(v_val_9_);
v___x_24_ = lean_apply_1(v_h__5_6_, v_ids_23_);
return v___x_24_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object* v_n_25_, lean_object* v_motive_26_, lean_object* v_step_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_, lean_object* v_h__4_31_, lean_object* v_h__5_32_){
_start:
{
if (lean_obj_tag(v_step_27_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__5_32_);
lean_dec(v_h__4_31_);
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__1_28_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_val_35_; 
lean_dec(v_h__1_28_);
v_val_35_ = lean_ctor_get(v_step_27_, 0);
lean_inc(v_val_35_);
lean_dec_ref(v_step_27_);
switch(lean_obj_tag(v_val_35_))
{
case 0:
{
lean_object* v_id_36_; lean_object* v_rupHints_37_; lean_object* v___x_38_; 
lean_dec(v_h__5_32_);
lean_dec(v_h__4_31_);
lean_dec(v_h__3_30_);
v_id_36_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_id_36_);
v_rupHints_37_ = lean_ctor_get(v_val_35_, 1);
lean_inc_ref(v_rupHints_37_);
lean_dec_ref(v_val_35_);
v___x_38_ = lean_apply_2(v_h__2_29_, v_id_36_, v_rupHints_37_);
return v___x_38_;
}
case 1:
{
lean_object* v_id_39_; lean_object* v_c_40_; lean_object* v_rupHints_41_; lean_object* v___x_42_; 
lean_dec(v_h__5_32_);
lean_dec(v_h__4_31_);
lean_dec(v_h__2_29_);
v_id_39_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_id_39_);
v_c_40_ = lean_ctor_get(v_val_35_, 1);
lean_inc(v_c_40_);
v_rupHints_41_ = lean_ctor_get(v_val_35_, 2);
lean_inc_ref(v_rupHints_41_);
lean_dec_ref(v_val_35_);
v___x_42_ = lean_apply_3(v_h__3_30_, v_id_39_, v_c_40_, v_rupHints_41_);
return v___x_42_;
}
case 2:
{
lean_object* v_id_43_; lean_object* v_c_44_; lean_object* v_pivot_45_; lean_object* v_rupHints_46_; lean_object* v_ratHints_47_; lean_object* v___x_48_; 
lean_dec(v_h__5_32_);
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v_id_43_ = lean_ctor_get(v_val_35_, 0);
lean_inc(v_id_43_);
v_c_44_ = lean_ctor_get(v_val_35_, 1);
lean_inc(v_c_44_);
v_pivot_45_ = lean_ctor_get(v_val_35_, 2);
lean_inc_ref(v_pivot_45_);
v_rupHints_46_ = lean_ctor_get(v_val_35_, 3);
lean_inc_ref(v_rupHints_46_);
v_ratHints_47_ = lean_ctor_get(v_val_35_, 4);
lean_inc_ref(v_ratHints_47_);
lean_dec_ref(v_val_35_);
v___x_48_ = lean_apply_5(v_h__4_31_, v_id_43_, v_c_44_, v_pivot_45_, v_rupHints_46_, v_ratHints_47_);
return v___x_48_;
}
default: 
{
lean_object* v_ids_49_; lean_object* v___x_50_; 
lean_dec(v_h__4_31_);
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v_ids_49_ = lean_ctor_get(v_val_35_, 0);
lean_inc_ref(v_ids_49_);
lean_dec_ref(v_val_35_);
v___x_50_ = lean_apply_1(v_h__5_32_, v_ids_49_);
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object* v_n_51_, lean_object* v_motive_52_, lean_object* v_step_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_, lean_object* v_h__4_57_, lean_object* v_h__5_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_51_, v_motive_52_, v_step_53_, v_h__1_54_, v_h__2_55_, v_h__3_56_, v_h__4_57_, v_h__5_58_);
lean_dec(v_n_51_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object* v_x_60_, lean_object* v_h__1_61_){
_start:
{
lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_64_; 
v_fst_62_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_fst_62_);
v_snd_63_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_snd_63_);
lean_dec_ref(v_x_60_);
v___x_64_ = lean_apply_2(v_h__1_61_, v_fst_62_, v_snd_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object* v_n_65_, lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_h__1_68_){
_start:
{
lean_object* v_fst_69_; lean_object* v_snd_70_; lean_object* v___x_71_; 
v_fst_69_ = lean_ctor_get(v_x_67_, 0);
lean_inc(v_fst_69_);
v_snd_70_ = lean_ctor_get(v_x_67_, 1);
lean_inc(v_snd_70_);
lean_dec_ref(v_x_67_);
v___x_71_ = lean_apply_2(v_h__1_68_, v_fst_69_, v_snd_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object* v_n_72_, lean_object* v_motive_73_, lean_object* v_x_74_, lean_object* v_h__1_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_72_, v_motive_73_, v_x_74_, v_h__1_75_);
lean_dec(v_n_72_);
return v_res_76_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATCheckerSound(builtin);
}
#ifdef __cplusplus
}
#endif
