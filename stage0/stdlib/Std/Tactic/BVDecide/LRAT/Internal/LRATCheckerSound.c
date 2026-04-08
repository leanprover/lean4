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
if (lean_obj_tag(v_prf_32_) == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_h__3_35_);
lean_dec(v_h__2_34_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__1_33_, v___x_38_);
return v___x_39_;
}
else
{
lean_object* v_head_40_; 
lean_dec(v_h__1_33_);
v_head_40_ = lean_ctor_get(v_prf_32_, 0);
lean_inc(v_head_40_);
switch(lean_obj_tag(v_head_40_))
{
case 0:
{
lean_object* v_tail_41_; lean_object* v_id_42_; lean_object* v_rupHints_43_; lean_object* v___x_44_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_h__3_35_);
v_tail_41_ = lean_ctor_get(v_prf_32_, 1);
lean_inc(v_tail_41_);
lean_dec_ref(v_prf_32_);
v_id_42_ = lean_ctor_get(v_head_40_, 0);
lean_inc(v_id_42_);
v_rupHints_43_ = lean_ctor_get(v_head_40_, 1);
lean_inc_ref(v_rupHints_43_);
lean_dec_ref(v_head_40_);
v___x_44_ = lean_apply_3(v_h__2_34_, v_id_42_, v_rupHints_43_, v_tail_41_);
return v___x_44_;
}
case 1:
{
lean_object* v_tail_45_; lean_object* v_id_46_; lean_object* v_c_47_; lean_object* v_rupHints_48_; lean_object* v___x_49_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__4_36_);
lean_dec(v_h__2_34_);
v_tail_45_ = lean_ctor_get(v_prf_32_, 1);
lean_inc(v_tail_45_);
lean_dec_ref(v_prf_32_);
v_id_46_ = lean_ctor_get(v_head_40_, 0);
lean_inc(v_id_46_);
v_c_47_ = lean_ctor_get(v_head_40_, 1);
lean_inc(v_c_47_);
v_rupHints_48_ = lean_ctor_get(v_head_40_, 2);
lean_inc_ref(v_rupHints_48_);
lean_dec_ref(v_head_40_);
v___x_49_ = lean_apply_4(v_h__3_35_, v_id_46_, v_c_47_, v_rupHints_48_, v_tail_45_);
return v___x_49_;
}
case 2:
{
lean_object* v_tail_50_; lean_object* v_id_51_; lean_object* v_c_52_; lean_object* v_pivot_53_; lean_object* v_rupHints_54_; lean_object* v_ratHints_55_; lean_object* v___x_56_; 
lean_dec(v_h__5_37_);
lean_dec(v_h__3_35_);
lean_dec(v_h__2_34_);
v_tail_50_ = lean_ctor_get(v_prf_32_, 1);
lean_inc(v_tail_50_);
lean_dec_ref(v_prf_32_);
v_id_51_ = lean_ctor_get(v_head_40_, 0);
lean_inc(v_id_51_);
v_c_52_ = lean_ctor_get(v_head_40_, 1);
lean_inc(v_c_52_);
v_pivot_53_ = lean_ctor_get(v_head_40_, 2);
lean_inc_ref(v_pivot_53_);
v_rupHints_54_ = lean_ctor_get(v_head_40_, 3);
lean_inc_ref(v_rupHints_54_);
v_ratHints_55_ = lean_ctor_get(v_head_40_, 4);
lean_inc_ref(v_ratHints_55_);
lean_dec_ref(v_head_40_);
v___x_56_ = lean_apply_6(v_h__4_36_, v_id_51_, v_c_52_, v_pivot_53_, v_rupHints_54_, v_ratHints_55_, v_tail_50_);
return v___x_56_;
}
default: 
{
lean_object* v_tail_57_; lean_object* v_ids_58_; lean_object* v___x_59_; 
lean_dec(v_h__4_36_);
lean_dec(v_h__3_35_);
lean_dec(v_h__2_34_);
v_tail_57_ = lean_ctor_get(v_prf_32_, 1);
lean_inc(v_tail_57_);
lean_dec_ref(v_prf_32_);
v_ids_58_ = lean_ctor_get(v_head_40_, 0);
lean_inc_ref(v_ids_58_);
lean_dec_ref(v_head_40_);
v___x_59_ = lean_apply_2(v_h__5_37_, v_ids_58_, v_tail_57_);
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter___redArg(lean_object* v_x_60_, lean_object* v_h__1_61_){
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_lratChecker_match__1_splitter(lean_object* v_00_u03c3_65_, lean_object* v_motive_66_, lean_object* v_x_67_, lean_object* v_h__1_68_){
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter___redArg(lean_object* v_x_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
if (lean_obj_tag(v_x_72_) == 2)
{
lean_object* v_id_75_; lean_object* v_c_76_; lean_object* v_pivot_77_; lean_object* v_rupHints_78_; lean_object* v_ratHints_79_; lean_object* v___x_80_; 
lean_dec(v_h__2_74_);
v_id_75_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_id_75_);
v_c_76_ = lean_ctor_get(v_x_72_, 1);
lean_inc(v_c_76_);
v_pivot_77_ = lean_ctor_get(v_x_72_, 2);
lean_inc_ref(v_pivot_77_);
v_rupHints_78_ = lean_ctor_get(v_x_72_, 3);
lean_inc_ref(v_rupHints_78_);
v_ratHints_79_ = lean_ctor_get(v_x_72_, 4);
lean_inc_ref(v_ratHints_79_);
lean_dec_ref(v_x_72_);
v___x_80_ = lean_apply_5(v_h__1_73_, v_id_75_, v_c_76_, v_pivot_77_, v_rupHints_78_, v_ratHints_79_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
lean_dec(v_h__1_73_);
v___x_81_ = lean_apply_2(v_h__2_74_, v_x_72_, lean_box(0));
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound_0__Std_Tactic_BVDecide_LRAT_Internal_WellFormedAction_match__1_splitter(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_motive_84_, lean_object* v_x_85_, lean_object* v_h__1_86_, lean_object* v_h__2_87_){
_start:
{
if (lean_obj_tag(v_x_85_) == 2)
{
lean_object* v_id_88_; lean_object* v_c_89_; lean_object* v_pivot_90_; lean_object* v_rupHints_91_; lean_object* v_ratHints_92_; lean_object* v___x_93_; 
lean_dec(v_h__2_87_);
v_id_88_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_id_88_);
v_c_89_ = lean_ctor_get(v_x_85_, 1);
lean_inc(v_c_89_);
v_pivot_90_ = lean_ctor_get(v_x_85_, 2);
lean_inc_ref(v_pivot_90_);
v_rupHints_91_ = lean_ctor_get(v_x_85_, 3);
lean_inc_ref(v_rupHints_91_);
v_ratHints_92_ = lean_ctor_get(v_x_85_, 4);
lean_inc_ref(v_ratHints_92_);
lean_dec_ref(v_x_85_);
v___x_93_ = lean_apply_5(v_h__1_86_, v_id_88_, v_c_89_, v_pivot_90_, v_rupHints_91_, v_ratHints_92_);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
lean_dec(v_h__1_86_);
v___x_94_ = lean_apply_2(v_h__2_87_, v_x_85_, lean_box(0));
return v___x_94_;
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
