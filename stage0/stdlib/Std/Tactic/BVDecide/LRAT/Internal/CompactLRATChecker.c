// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.CompactLRATChecker
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.LRATChecker public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation public import Std.Tactic.BVDecide.LRAT.Internal.Formula.Instance public import Std.Tactic.BVDecide.LRAT.Internal.Actions
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(uint8_t v___x_1_, uint8_t v___y_2_, uint8_t v___y_3_){
_start:
{
if (v___y_2_ == 0)
{
if (v___y_3_ == 0)
{
return v___x_1_;
}
else
{
return v___y_2_;
}
}
else
{
return v___y_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed(lean_object* v___x_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
uint8_t v___x_429__boxed_7_; uint8_t v___y_430__boxed_8_; uint8_t v___y_431__boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v___x_429__boxed_7_ = lean_unbox(v___x_4_);
v___y_430__boxed_8_ = lean_unbox(v___y_5_);
v___y_431__boxed_9_ = lean_unbox(v___y_6_);
v_res_10_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0(v___x_429__boxed_7_, v___y_430__boxed_8_, v___y_431__boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(lean_object* v_n_12_, lean_object* v_f_13_, lean_object* v_proof_14_, lean_object* v_idx_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = lean_array_get_size(v_proof_14_);
v___x_17_ = lean_nat_dec_lt(v_idx_15_, v___x_16_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
lean_dec(v_idx_15_);
lean_dec_ref(v_f_13_);
lean_dec(v_n_12_);
v___x_18_ = 1;
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v_step_20_; 
v___x_19_ = lean_array_fget_borrowed(v_proof_14_, v_idx_15_);
lean_inc(v___x_19_);
v_step_20_ = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(v_n_12_, v___x_19_);
if (lean_obj_tag(v_step_20_) == 0)
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_add(v_idx_15_, v___x_21_);
lean_dec(v_idx_15_);
v_idx_15_ = v___x_22_;
goto _start;
}
else
{
lean_object* v_val_24_; 
v_val_24_ = lean_ctor_get(v_step_20_, 0);
lean_inc(v_val_24_);
lean_dec_ref(v_step_20_);
switch(lean_obj_tag(v_val_24_))
{
case 0:
{
lean_object* v_rupHints_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_snd_28_; uint8_t v___x_29_; 
lean_dec(v_idx_15_);
v_rupHints_25_ = lean_ctor_get(v_val_24_, 1);
lean_inc_ref(v_rupHints_25_);
lean_dec_ref(v_val_24_);
v___x_26_ = lean_box(0);
v___x_27_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_12_, v_f_13_, v___x_26_, v_rupHints_25_);
lean_dec_ref(v_rupHints_25_);
lean_dec(v_n_12_);
v_snd_28_ = lean_ctor_get(v___x_27_, 1);
lean_inc(v_snd_28_);
lean_dec_ref(v___x_27_);
v___x_29_ = lean_unbox(v_snd_28_);
lean_dec(v_snd_28_);
if (v___x_29_ == 0)
{
uint8_t v___x_30_; 
v___x_30_ = 2;
return v___x_30_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
}
case 1:
{
lean_object* v_c_32_; lean_object* v_rupHints_33_; lean_object* v___x_34_; lean_object* v_snd_35_; uint8_t v___x_36_; 
v_c_32_ = lean_ctor_get(v_val_24_, 1);
lean_inc(v_c_32_);
v_rupHints_33_ = lean_ctor_get(v_val_24_, 2);
lean_inc_ref(v_rupHints_33_);
lean_dec_ref(v_val_24_);
v___x_34_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_12_, v_f_13_, v_c_32_, v_rupHints_33_);
lean_dec_ref(v_rupHints_33_);
v_snd_35_ = lean_ctor_get(v___x_34_, 1);
lean_inc(v_snd_35_);
v___x_36_ = lean_unbox(v_snd_35_);
lean_dec(v_snd_35_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; 
lean_dec_ref(v___x_34_);
lean_dec(v_idx_15_);
lean_dec(v_n_12_);
v___x_37_ = 2;
return v___x_37_;
}
else
{
lean_object* v_fst_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_fst_38_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_fst_38_);
lean_dec_ref(v___x_34_);
v___x_39_ = lean_unsigned_to_nat(1u);
v___x_40_ = lean_nat_add(v_idx_15_, v___x_39_);
lean_dec(v_idx_15_);
v_f_13_ = v_fst_38_;
v_idx_15_ = v___x_40_;
goto _start;
}
}
case 2:
{
lean_object* v_c_42_; lean_object* v_pivot_43_; lean_object* v_rupHints_44_; lean_object* v_ratHints_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___f_51_; uint8_t v___x_52_; 
v_c_42_ = lean_ctor_get(v_val_24_, 1);
lean_inc(v_c_42_);
v_pivot_43_ = lean_ctor_get(v_val_24_, 2);
lean_inc_ref(v_pivot_43_);
v_rupHints_44_ = lean_ctor_get(v_val_24_, 3);
lean_inc_ref(v_rupHints_44_);
v_ratHints_45_ = lean_ctor_get(v_val_24_, 4);
lean_inc_ref(v_ratHints_45_);
lean_dec_ref(v_val_24_);
v___x_46_ = lean_box(v___x_17_);
v___f_47_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___lam__0___boxed), 3, 1);
lean_closure_set(v___f_47_, 0, v___x_46_);
lean_inc(v_n_12_);
v___x_48_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(v___x_48_, 0, v_n_12_);
v___f_49_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_49_, 0, v___x_48_);
v___f_50_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_50_, 0, v___f_47_);
v___f_51_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_51_, 0, v___f_49_);
lean_closure_set(v___f_51_, 1, v___f_50_);
lean_inc(v_c_42_);
lean_inc_ref(v_pivot_43_);
v___x_52_ = l_List_elem___redArg(v___f_51_, v_pivot_43_, v_c_42_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec_ref(v_ratHints_45_);
lean_dec_ref(v_rupHints_44_);
lean_dec_ref(v_pivot_43_);
lean_dec(v_c_42_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_idx_15_, v___x_53_);
lean_dec(v_idx_15_);
v_idx_15_ = v___x_54_;
goto _start;
}
else
{
lean_object* v___x_56_; lean_object* v_snd_57_; uint8_t v___x_58_; 
v___x_56_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_12_, v_f_13_, v_c_42_, v_pivot_43_, v_rupHints_44_, v_ratHints_45_);
lean_dec_ref(v_rupHints_44_);
v_snd_57_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_snd_57_);
v___x_58_ = lean_unbox(v_snd_57_);
lean_dec(v_snd_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
lean_dec_ref(v___x_56_);
lean_dec(v_idx_15_);
lean_dec(v_n_12_);
v___x_59_ = 2;
return v___x_59_;
}
else
{
lean_object* v_fst_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_fst_60_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_fst_60_);
lean_dec_ref(v___x_56_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_idx_15_, v___x_61_);
lean_dec(v_idx_15_);
v_f_13_ = v_fst_60_;
v_idx_15_ = v___x_62_;
goto _start;
}
}
}
default: 
{
lean_object* v_ids_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_ids_64_ = lean_ctor_get(v_val_24_, 0);
lean_inc_ref(v_ids_64_);
lean_dec_ref(v_val_24_);
v___x_65_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(v_n_12_, v_f_13_, v_ids_64_);
lean_dec_ref(v_ids_64_);
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_idx_15_, v___x_66_);
lean_dec(v_idx_15_);
v_f_13_ = v___x_65_;
v_idx_15_ = v___x_67_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___boxed(lean_object* v_n_69_, lean_object* v_f_70_, lean_object* v_proof_71_, lean_object* v_idx_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(v_n_69_, v_f_70_, v_proof_71_, v_idx_72_);
lean_dec_ref(v_proof_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object* v_step_75_, lean_object* v_h__1_76_, lean_object* v_h__2_77_, lean_object* v_h__3_78_, lean_object* v_h__4_79_, lean_object* v_h__5_80_){
_start:
{
if (lean_obj_tag(v_step_75_) == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
v___x_81_ = lean_box(0);
v___x_82_ = lean_apply_1(v_h__1_76_, v___x_81_);
return v___x_82_;
}
else
{
lean_object* v_val_83_; 
lean_dec(v_h__1_76_);
v_val_83_ = lean_ctor_get(v_step_75_, 0);
lean_inc(v_val_83_);
lean_dec_ref(v_step_75_);
switch(lean_obj_tag(v_val_83_))
{
case 0:
{
lean_object* v_id_84_; lean_object* v_rupHints_85_; lean_object* v___x_86_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_h__3_78_);
v_id_84_ = lean_ctor_get(v_val_83_, 0);
lean_inc(v_id_84_);
v_rupHints_85_ = lean_ctor_get(v_val_83_, 1);
lean_inc_ref(v_rupHints_85_);
lean_dec_ref(v_val_83_);
v___x_86_ = lean_apply_2(v_h__2_77_, v_id_84_, v_rupHints_85_);
return v___x_86_;
}
case 1:
{
lean_object* v_id_87_; lean_object* v_c_88_; lean_object* v_rupHints_89_; lean_object* v___x_90_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__4_79_);
lean_dec(v_h__2_77_);
v_id_87_ = lean_ctor_get(v_val_83_, 0);
lean_inc(v_id_87_);
v_c_88_ = lean_ctor_get(v_val_83_, 1);
lean_inc(v_c_88_);
v_rupHints_89_ = lean_ctor_get(v_val_83_, 2);
lean_inc_ref(v_rupHints_89_);
lean_dec_ref(v_val_83_);
v___x_90_ = lean_apply_3(v_h__3_78_, v_id_87_, v_c_88_, v_rupHints_89_);
return v___x_90_;
}
case 2:
{
lean_object* v_id_91_; lean_object* v_c_92_; lean_object* v_pivot_93_; lean_object* v_rupHints_94_; lean_object* v_ratHints_95_; lean_object* v___x_96_; 
lean_dec(v_h__5_80_);
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
v_id_91_ = lean_ctor_get(v_val_83_, 0);
lean_inc(v_id_91_);
v_c_92_ = lean_ctor_get(v_val_83_, 1);
lean_inc(v_c_92_);
v_pivot_93_ = lean_ctor_get(v_val_83_, 2);
lean_inc_ref(v_pivot_93_);
v_rupHints_94_ = lean_ctor_get(v_val_83_, 3);
lean_inc_ref(v_rupHints_94_);
v_ratHints_95_ = lean_ctor_get(v_val_83_, 4);
lean_inc_ref(v_ratHints_95_);
lean_dec_ref(v_val_83_);
v___x_96_ = lean_apply_5(v_h__4_79_, v_id_91_, v_c_92_, v_pivot_93_, v_rupHints_94_, v_ratHints_95_);
return v___x_96_;
}
default: 
{
lean_object* v_ids_97_; lean_object* v___x_98_; 
lean_dec(v_h__4_79_);
lean_dec(v_h__3_78_);
lean_dec(v_h__2_77_);
v_ids_97_ = lean_ctor_get(v_val_83_, 0);
lean_inc_ref(v_ids_97_);
lean_dec_ref(v_val_83_);
v___x_98_ = lean_apply_1(v_h__5_80_, v_ids_97_);
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object* v_n_99_, lean_object* v_motive_100_, lean_object* v_step_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_, lean_object* v_h__3_104_, lean_object* v_h__4_105_, lean_object* v_h__5_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(v_step_101_, v_h__1_102_, v_h__2_103_, v_h__3_104_, v_h__4_105_, v_h__5_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object* v_n_108_, lean_object* v_motive_109_, lean_object* v_step_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_, lean_object* v_h__4_114_, lean_object* v_h__5_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_108_, v_motive_109_, v_step_110_, v_h__1_111_, v_h__2_112_, v_h__3_113_, v_h__4_114_, v_h__5_115_);
lean_dec(v_n_108_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_h__1_118_){
_start:
{
lean_object* v_fst_119_; lean_object* v_snd_120_; lean_object* v___x_121_; 
v_fst_119_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_fst_119_);
v_snd_120_ = lean_ctor_get(v_x_117_, 1);
lean_inc(v_snd_120_);
lean_dec_ref(v_x_117_);
v___x_121_ = lean_apply_2(v_h__1_118_, v_fst_119_, v_snd_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object* v_n_122_, lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_h__1_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(v_x_124_, v_h__1_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object* v_n_127_, lean_object* v_motive_128_, lean_object* v_x_129_, lean_object* v_h__1_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_127_, v_motive_128_, v_x_129_, v_h__1_130_);
lean_dec(v_n_127_);
return v_res_131_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object* v_n_132_, lean_object* v_f_133_, lean_object* v_proof_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(v_n_132_, v_f_133_, v_proof_134_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(lean_object* v_n_137_, lean_object* v_f_138_, lean_object* v_proof_139_){
_start:
{
uint8_t v_res_140_; lean_object* v_r_141_; 
v_res_140_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v_n_137_, v_f_138_, v_proof_139_);
lean_dec_ref(v_proof_139_);
v_r_141_ = lean_box(v_res_140_);
return v_r_141_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(builtin);
}
#ifdef __cplusplus
}
#endif
