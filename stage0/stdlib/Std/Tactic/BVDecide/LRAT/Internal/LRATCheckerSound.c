// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker public import Std.Tactic.BVDecide.LRAT.Internal.CNF public import Std.Tactic.BVDecide.LRAT.Internal.Actions
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter___redArg(lean_object* v_prf_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_, lean_object* v_h__5_6_){
_start:
{
if (lean_obj_tag(v_prf_1_) == 0)
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
lean_object* v_head_9_; 
lean_dec(v_h__1_2_);
v_head_9_ = lean_ctor_get(v_prf_1_, 0);
lean_inc(v_head_9_);
switch(lean_obj_tag(v_head_9_))
{
case 0:
{
lean_object* v_tail_10_; lean_object* v_id_11_; lean_object* v_rupHints_12_; lean_object* v___x_13_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
v_tail_10_ = lean_ctor_get(v_prf_1_, 1);
lean_inc(v_tail_10_);
lean_dec_ref(v_prf_1_);
v_id_11_ = lean_ctor_get(v_head_9_, 0);
lean_inc(v_id_11_);
v_rupHints_12_ = lean_ctor_get(v_head_9_, 1);
lean_inc_ref(v_rupHints_12_);
lean_dec_ref(v_head_9_);
v___x_13_ = lean_apply_3(v_h__2_3_, v_id_11_, v_rupHints_12_, v_tail_10_);
return v___x_13_;
}
case 1:
{
lean_object* v_tail_14_; lean_object* v_id_15_; lean_object* v_c_16_; lean_object* v_rupHints_17_; lean_object* v___x_18_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
v_tail_14_ = lean_ctor_get(v_prf_1_, 1);
lean_inc(v_tail_14_);
lean_dec_ref(v_prf_1_);
v_id_15_ = lean_ctor_get(v_head_9_, 0);
lean_inc(v_id_15_);
v_c_16_ = lean_ctor_get(v_head_9_, 1);
lean_inc(v_c_16_);
v_rupHints_17_ = lean_ctor_get(v_head_9_, 2);
lean_inc_ref(v_rupHints_17_);
lean_dec_ref(v_head_9_);
v___x_18_ = lean_apply_4(v_h__3_4_, v_id_15_, v_c_16_, v_rupHints_17_, v_tail_14_);
return v___x_18_;
}
case 2:
{
lean_object* v_tail_19_; lean_object* v_id_20_; lean_object* v_c_21_; lean_object* v_pivot_22_; lean_object* v_rupHints_23_; lean_object* v_ratHints_24_; lean_object* v___x_25_; 
lean_dec(v_h__5_6_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_tail_19_ = lean_ctor_get(v_prf_1_, 1);
lean_inc(v_tail_19_);
lean_dec_ref(v_prf_1_);
v_id_20_ = lean_ctor_get(v_head_9_, 0);
lean_inc(v_id_20_);
v_c_21_ = lean_ctor_get(v_head_9_, 1);
lean_inc(v_c_21_);
v_pivot_22_ = lean_ctor_get(v_head_9_, 2);
lean_inc_ref(v_pivot_22_);
v_rupHints_23_ = lean_ctor_get(v_head_9_, 3);
lean_inc_ref(v_rupHints_23_);
v_ratHints_24_ = lean_ctor_get(v_head_9_, 4);
lean_inc_ref(v_ratHints_24_);
lean_dec_ref(v_head_9_);
v___x_25_ = lean_apply_6(v_h__4_5_, v_id_20_, v_c_21_, v_pivot_22_, v_rupHints_23_, v_ratHints_24_, v_tail_19_);
return v___x_25_;
}
default: 
{
lean_object* v_tail_26_; lean_object* v_ids_27_; lean_object* v___x_28_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_tail_26_ = lean_ctor_get(v_prf_1_, 1);
lean_inc(v_tail_26_);
lean_dec_ref(v_prf_1_);
v_ids_27_ = lean_ctor_get(v_head_9_, 0);
lean_inc_ref(v_ids_27_);
lean_dec_ref(v_head_9_);
v___x_28_ = lean_apply_2(v_h__5_6_, v_ids_27_, v_tail_26_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_motive_31_, lean_object* v_prf_32_, lean_object* v_h__1_33_, lean_object* v_h__2_34_, lean_object* v_h__3_35_, lean_object* v_h__4_36_, lean_object* v_h__5_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__3_splitter___redArg(v_prf_32_, v_h__1_33_, v_h__2_34_, v_h__3_35_, v_h__4_36_, v_h__5_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(lean_object* v_x_39_, lean_object* v_h__1_40_){
_start:
{
lean_object* v_fst_41_; lean_object* v_snd_42_; lean_object* v___x_43_; 
v_fst_41_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_fst_41_);
v_snd_42_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_snd_42_);
lean_dec_ref(v_x_39_);
v___x_43_ = lean_apply_2(v_h__1_40_, v_fst_41_, v_snd_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(lean_object* v_00_u03c3_44_, lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(v_x_46_, v_h__1_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(lean_object* v_x_49_, lean_object* v_h__1_50_, lean_object* v_h__2_51_){
_start:
{
if (lean_obj_tag(v_x_49_) == 2)
{
lean_object* v_id_52_; lean_object* v_c_53_; lean_object* v_pivot_54_; lean_object* v_rupHints_55_; lean_object* v_ratHints_56_; lean_object* v___x_57_; 
lean_dec(v_h__2_51_);
v_id_52_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_id_52_);
v_c_53_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_c_53_);
v_pivot_54_ = lean_ctor_get(v_x_49_, 2);
lean_inc_ref(v_pivot_54_);
v_rupHints_55_ = lean_ctor_get(v_x_49_, 3);
lean_inc_ref(v_rupHints_55_);
v_ratHints_56_ = lean_ctor_get(v_x_49_, 4);
lean_inc_ref(v_ratHints_56_);
lean_dec_ref(v_x_49_);
v___x_57_ = lean_apply_5(v_h__1_50_, v_id_52_, v_c_53_, v_pivot_54_, v_rupHints_55_, v_ratHints_56_);
return v___x_57_;
}
else
{
lean_object* v___x_58_; 
lean_dec(v_h__1_50_);
v___x_58_ = lean_apply_2(v_h__2_51_, v_x_49_, lean_box(0));
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_motive_61_, lean_object* v_x_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
if (lean_obj_tag(v_x_62_) == 2)
{
lean_object* v_id_65_; lean_object* v_c_66_; lean_object* v_pivot_67_; lean_object* v_rupHints_68_; lean_object* v_ratHints_69_; lean_object* v___x_70_; 
lean_dec(v_h__2_64_);
v_id_65_ = lean_ctor_get(v_x_62_, 0);
lean_inc(v_id_65_);
v_c_66_ = lean_ctor_get(v_x_62_, 1);
lean_inc(v_c_66_);
v_pivot_67_ = lean_ctor_get(v_x_62_, 2);
lean_inc_ref(v_pivot_67_);
v_rupHints_68_ = lean_ctor_get(v_x_62_, 3);
lean_inc_ref(v_rupHints_68_);
v_ratHints_69_ = lean_ctor_get(v_x_62_, 4);
lean_inc_ref(v_ratHints_69_);
lean_dec_ref(v_x_62_);
v___x_70_ = lean_apply_5(v_h__1_63_, v_id_65_, v_c_66_, v_pivot_67_, v_rupHints_68_, v_ratHints_69_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; 
lean_dec(v_h__1_63_);
v___x_71_ = lean_apply_2(v_h__2_64_, v_x_62_, lean_box(0));
return v___x_71_;
}
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin);
}
#ifdef __cplusplus
}
#endif
