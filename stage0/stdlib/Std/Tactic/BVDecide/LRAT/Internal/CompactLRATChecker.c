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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg(lean_object* v_idx_1_, lean_object* v___x_2_, lean_object* v_a_3_, lean_object* v_x_4_){
_start:
{
if (lean_obj_tag(v_x_4_) == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
else
{
lean_object* v_head_6_; lean_object* v_tail_7_; uint8_t v___y_9_; lean_object* v_fst_11_; lean_object* v_snd_12_; lean_object* v_fst_13_; lean_object* v_snd_14_; uint8_t v___x_15_; 
v_head_6_ = lean_ctor_get(v_x_4_, 0);
v_tail_7_ = lean_ctor_get(v_x_4_, 1);
v_fst_11_ = lean_ctor_get(v_a_3_, 0);
v_snd_12_ = lean_ctor_get(v_a_3_, 1);
v_fst_13_ = lean_ctor_get(v_head_6_, 0);
v_snd_14_ = lean_ctor_get(v_head_6_, 1);
v___x_15_ = lean_nat_dec_eq(v_fst_11_, v_fst_13_);
if (v___x_15_ == 0)
{
v_x_4_ = v_tail_7_;
goto _start;
}
else
{
uint8_t v___x_17_; 
v___x_17_ = lean_unbox(v_snd_14_);
if (v___x_17_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = lean_unbox(v_snd_12_);
if (v___x_18_ == 0)
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_lt(v_idx_1_, v___x_2_);
v___y_9_ = v___x_19_;
goto v___jp_8_;
}
else
{
v_x_4_ = v_tail_7_;
goto _start;
}
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_unbox(v_snd_12_);
v___y_9_ = v___x_21_;
goto v___jp_8_;
}
}
v___jp_8_:
{
if (v___y_9_ == 0)
{
v_x_4_ = v_tail_7_;
goto _start;
}
else
{
return v___y_9_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg___boxed(lean_object* v_idx_22_, lean_object* v___x_23_, lean_object* v_a_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg(v_idx_22_, v___x_23_, v_a_24_, v_x_25_);
lean_dec(v_x_25_);
lean_dec_ref(v_a_24_);
lean_dec(v___x_23_);
lean_dec(v_idx_22_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(lean_object* v_n_28_, lean_object* v_f_29_, lean_object* v_proof_30_, lean_object* v_idx_31_){
_start:
{
lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_32_ = lean_array_get_size(v_proof_30_);
v___x_33_ = lean_nat_dec_lt(v_idx_31_, v___x_32_);
if (v___x_33_ == 0)
{
uint8_t v___x_34_; 
lean_dec(v_idx_31_);
lean_dec_ref(v_f_29_);
v___x_34_ = 1;
return v___x_34_;
}
else
{
lean_object* v___x_35_; lean_object* v_step_36_; 
v___x_35_ = lean_array_fget_borrowed(v_proof_30_, v_idx_31_);
lean_inc(v___x_35_);
v_step_36_ = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(v_n_28_, v___x_35_);
if (lean_obj_tag(v_step_36_) == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_idx_31_, v___x_37_);
lean_dec(v_idx_31_);
v_idx_31_ = v___x_38_;
goto _start;
}
else
{
lean_object* v_val_40_; 
v_val_40_ = lean_ctor_get(v_step_36_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v_step_36_, 1);
switch(lean_obj_tag(v_val_40_))
{
case 0:
{
lean_object* v_rupHints_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v_snd_44_; uint8_t v___x_45_; 
lean_dec(v_idx_31_);
v_rupHints_41_ = lean_ctor_get(v_val_40_, 1);
lean_inc_ref(v_rupHints_41_);
lean_dec_ref_known(v_val_40_, 2);
v___x_42_ = lean_box(0);
v___x_43_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_28_, v_f_29_, v___x_42_, v_rupHints_41_);
lean_dec_ref(v_rupHints_41_);
v_snd_44_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_snd_44_);
lean_dec_ref(v___x_43_);
v___x_45_ = lean_unbox(v_snd_44_);
lean_dec(v_snd_44_);
if (v___x_45_ == 0)
{
uint8_t v___x_46_; 
v___x_46_ = 2;
return v___x_46_;
}
else
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
}
case 1:
{
lean_object* v_c_48_; lean_object* v_rupHints_49_; lean_object* v___x_50_; lean_object* v_snd_51_; uint8_t v___x_52_; 
v_c_48_ = lean_ctor_get(v_val_40_, 1);
lean_inc(v_c_48_);
v_rupHints_49_ = lean_ctor_get(v_val_40_, 2);
lean_inc_ref(v_rupHints_49_);
lean_dec_ref_known(v_val_40_, 3);
v___x_50_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(v_n_28_, v_f_29_, v_c_48_, v_rupHints_49_);
lean_dec_ref(v_rupHints_49_);
v_snd_51_ = lean_ctor_get(v___x_50_, 1);
lean_inc(v_snd_51_);
v___x_52_ = lean_unbox(v_snd_51_);
lean_dec(v_snd_51_);
if (v___x_52_ == 0)
{
uint8_t v___x_53_; 
lean_dec_ref(v___x_50_);
lean_dec(v_idx_31_);
v___x_53_ = 2;
return v___x_53_;
}
else
{
lean_object* v_fst_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_fst_54_ = lean_ctor_get(v___x_50_, 0);
lean_inc(v_fst_54_);
lean_dec_ref(v___x_50_);
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = lean_nat_add(v_idx_31_, v___x_55_);
lean_dec(v_idx_31_);
v_f_29_ = v_fst_54_;
v_idx_31_ = v___x_56_;
goto _start;
}
}
case 2:
{
lean_object* v_c_58_; lean_object* v_pivot_59_; lean_object* v_rupHints_60_; lean_object* v_ratHints_61_; uint8_t v___x_62_; 
v_c_58_ = lean_ctor_get(v_val_40_, 1);
lean_inc(v_c_58_);
v_pivot_59_ = lean_ctor_get(v_val_40_, 2);
lean_inc_ref(v_pivot_59_);
v_rupHints_60_ = lean_ctor_get(v_val_40_, 3);
lean_inc_ref(v_rupHints_60_);
v_ratHints_61_ = lean_ctor_get(v_val_40_, 4);
lean_inc_ref(v_ratHints_61_);
lean_dec_ref_known(v_val_40_, 5);
v___x_62_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg(v_idx_31_, v___x_32_, v_pivot_59_, v_c_58_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec_ref(v_ratHints_61_);
lean_dec_ref(v_rupHints_60_);
lean_dec_ref(v_pivot_59_);
lean_dec(v_c_58_);
v___x_63_ = lean_unsigned_to_nat(1u);
v___x_64_ = lean_nat_add(v_idx_31_, v___x_63_);
lean_dec(v_idx_31_);
v_idx_31_ = v___x_64_;
goto _start;
}
else
{
lean_object* v___x_66_; lean_object* v_fst_67_; lean_object* v_snd_68_; uint8_t v___y_70_; 
v___x_66_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(v_n_28_, v_f_29_, v_c_58_, v_pivot_59_, v_rupHints_60_, v_ratHints_61_);
lean_dec_ref(v_rupHints_60_);
v_fst_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_fst_67_);
v_snd_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_snd_68_);
lean_dec_ref(v___x_66_);
if (v___x_62_ == 0)
{
lean_dec(v_snd_68_);
v___y_70_ = v___x_62_;
goto v___jp_69_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = lean_unbox(v_snd_68_);
lean_dec(v_snd_68_);
v___y_70_ = v___x_75_;
goto v___jp_69_;
}
v___jp_69_:
{
if (v___y_70_ == 0)
{
uint8_t v___x_71_; 
lean_dec(v_fst_67_);
lean_dec(v_idx_31_);
v___x_71_ = 2;
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_idx_31_, v___x_72_);
lean_dec(v_idx_31_);
v_f_29_ = v_fst_67_;
v_idx_31_ = v___x_73_;
goto _start;
}
}
}
}
default: 
{
lean_object* v_ids_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_ids_76_ = lean_ctor_get(v_val_40_, 0);
lean_inc_ref(v_ids_76_);
lean_dec_ref_known(v_val_40_, 1);
v___x_77_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(v_n_28_, v_f_29_, v_ids_76_);
lean_dec_ref(v_ids_76_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_idx_31_, v___x_78_);
lean_dec(v_idx_31_);
v_f_29_ = v___x_77_;
v_idx_31_ = v___x_79_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go___boxed(lean_object* v_n_81_, lean_object* v_f_82_, lean_object* v_proof_83_, lean_object* v_idx_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(v_n_81_, v_f_82_, v_proof_83_, v_idx_84_);
lean_dec_ref(v_proof_83_);
lean_dec(v_n_81_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0(lean_object* v_n_87_, lean_object* v_idx_88_, lean_object* v___x_89_, lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___redArg(v_idx_88_, v___x_89_, v_a_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0___boxed(lean_object* v_n_93_, lean_object* v_idx_94_, lean_object* v___x_95_, lean_object* v_a_96_, lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_spec__0(v_n_93_, v_idx_94_, v___x_95_, v_a_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec_ref(v_a_96_);
lean_dec(v___x_95_);
lean_dec(v_idx_94_);
lean_dec(v_n_93_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___redArg(lean_object* v_step_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_, lean_object* v_h__4_104_, lean_object* v_h__5_105_){
_start:
{
if (lean_obj_tag(v_step_100_) == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v_h__5_105_);
lean_dec(v_h__4_104_);
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_apply_1(v_h__1_101_, v___x_106_);
return v___x_107_;
}
else
{
lean_object* v_val_108_; 
lean_dec(v_h__1_101_);
v_val_108_ = lean_ctor_get(v_step_100_, 0);
lean_inc(v_val_108_);
lean_dec_ref_known(v_step_100_, 1);
switch(lean_obj_tag(v_val_108_))
{
case 0:
{
lean_object* v_id_109_; lean_object* v_rupHints_110_; lean_object* v___x_111_; 
lean_dec(v_h__5_105_);
lean_dec(v_h__4_104_);
lean_dec(v_h__3_103_);
v_id_109_ = lean_ctor_get(v_val_108_, 0);
lean_inc(v_id_109_);
v_rupHints_110_ = lean_ctor_get(v_val_108_, 1);
lean_inc_ref(v_rupHints_110_);
lean_dec_ref_known(v_val_108_, 2);
v___x_111_ = lean_apply_2(v_h__2_102_, v_id_109_, v_rupHints_110_);
return v___x_111_;
}
case 1:
{
lean_object* v_id_112_; lean_object* v_c_113_; lean_object* v_rupHints_114_; lean_object* v___x_115_; 
lean_dec(v_h__5_105_);
lean_dec(v_h__4_104_);
lean_dec(v_h__2_102_);
v_id_112_ = lean_ctor_get(v_val_108_, 0);
lean_inc(v_id_112_);
v_c_113_ = lean_ctor_get(v_val_108_, 1);
lean_inc(v_c_113_);
v_rupHints_114_ = lean_ctor_get(v_val_108_, 2);
lean_inc_ref(v_rupHints_114_);
lean_dec_ref_known(v_val_108_, 3);
v___x_115_ = lean_apply_3(v_h__3_103_, v_id_112_, v_c_113_, v_rupHints_114_);
return v___x_115_;
}
case 2:
{
lean_object* v_id_116_; lean_object* v_c_117_; lean_object* v_pivot_118_; lean_object* v_rupHints_119_; lean_object* v_ratHints_120_; lean_object* v___x_121_; 
lean_dec(v_h__5_105_);
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v_id_116_ = lean_ctor_get(v_val_108_, 0);
lean_inc(v_id_116_);
v_c_117_ = lean_ctor_get(v_val_108_, 1);
lean_inc(v_c_117_);
v_pivot_118_ = lean_ctor_get(v_val_108_, 2);
lean_inc_ref(v_pivot_118_);
v_rupHints_119_ = lean_ctor_get(v_val_108_, 3);
lean_inc_ref(v_rupHints_119_);
v_ratHints_120_ = lean_ctor_get(v_val_108_, 4);
lean_inc_ref(v_ratHints_120_);
lean_dec_ref_known(v_val_108_, 5);
v___x_121_ = lean_apply_5(v_h__4_104_, v_id_116_, v_c_117_, v_pivot_118_, v_rupHints_119_, v_ratHints_120_);
return v___x_121_;
}
default: 
{
lean_object* v_ids_122_; lean_object* v___x_123_; 
lean_dec(v_h__4_104_);
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v_ids_122_ = lean_ctor_get(v_val_108_, 0);
lean_inc_ref(v_ids_122_);
lean_dec_ref_known(v_val_108_, 1);
v___x_123_ = lean_apply_1(v_h__5_105_, v_ids_122_);
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(lean_object* v_n_124_, lean_object* v_motive_125_, lean_object* v_step_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_, lean_object* v_h__3_129_, lean_object* v_h__4_130_, lean_object* v_h__5_131_){
_start:
{
if (lean_obj_tag(v_step_126_) == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__5_131_);
lean_dec(v_h__4_130_);
lean_dec(v_h__3_129_);
lean_dec(v_h__2_128_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__1_127_, v___x_132_);
return v___x_133_;
}
else
{
lean_object* v_val_134_; 
lean_dec(v_h__1_127_);
v_val_134_ = lean_ctor_get(v_step_126_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v_step_126_, 1);
switch(lean_obj_tag(v_val_134_))
{
case 0:
{
lean_object* v_id_135_; lean_object* v_rupHints_136_; lean_object* v___x_137_; 
lean_dec(v_h__5_131_);
lean_dec(v_h__4_130_);
lean_dec(v_h__3_129_);
v_id_135_ = lean_ctor_get(v_val_134_, 0);
lean_inc(v_id_135_);
v_rupHints_136_ = lean_ctor_get(v_val_134_, 1);
lean_inc_ref(v_rupHints_136_);
lean_dec_ref_known(v_val_134_, 2);
v___x_137_ = lean_apply_2(v_h__2_128_, v_id_135_, v_rupHints_136_);
return v___x_137_;
}
case 1:
{
lean_object* v_id_138_; lean_object* v_c_139_; lean_object* v_rupHints_140_; lean_object* v___x_141_; 
lean_dec(v_h__5_131_);
lean_dec(v_h__4_130_);
lean_dec(v_h__2_128_);
v_id_138_ = lean_ctor_get(v_val_134_, 0);
lean_inc(v_id_138_);
v_c_139_ = lean_ctor_get(v_val_134_, 1);
lean_inc(v_c_139_);
v_rupHints_140_ = lean_ctor_get(v_val_134_, 2);
lean_inc_ref(v_rupHints_140_);
lean_dec_ref_known(v_val_134_, 3);
v___x_141_ = lean_apply_3(v_h__3_129_, v_id_138_, v_c_139_, v_rupHints_140_);
return v___x_141_;
}
case 2:
{
lean_object* v_id_142_; lean_object* v_c_143_; lean_object* v_pivot_144_; lean_object* v_rupHints_145_; lean_object* v_ratHints_146_; lean_object* v___x_147_; 
lean_dec(v_h__5_131_);
lean_dec(v_h__3_129_);
lean_dec(v_h__2_128_);
v_id_142_ = lean_ctor_get(v_val_134_, 0);
lean_inc(v_id_142_);
v_c_143_ = lean_ctor_get(v_val_134_, 1);
lean_inc(v_c_143_);
v_pivot_144_ = lean_ctor_get(v_val_134_, 2);
lean_inc_ref(v_pivot_144_);
v_rupHints_145_ = lean_ctor_get(v_val_134_, 3);
lean_inc_ref(v_rupHints_145_);
v_ratHints_146_ = lean_ctor_get(v_val_134_, 4);
lean_inc_ref(v_ratHints_146_);
lean_dec_ref_known(v_val_134_, 5);
v___x_147_ = lean_apply_5(v_h__4_130_, v_id_142_, v_c_143_, v_pivot_144_, v_rupHints_145_, v_ratHints_146_);
return v___x_147_;
}
default: 
{
lean_object* v_ids_148_; lean_object* v___x_149_; 
lean_dec(v_h__4_130_);
lean_dec(v_h__3_129_);
lean_dec(v_h__2_128_);
v_ids_148_ = lean_ctor_get(v_val_134_, 0);
lean_inc_ref(v_ids_148_);
lean_dec_ref_known(v_val_134_, 1);
v___x_149_ = lean_apply_1(v_h__5_131_, v_ids_148_);
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter___boxed(lean_object* v_n_150_, lean_object* v_motive_151_, lean_object* v_step_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_, lean_object* v_h__3_155_, lean_object* v_h__4_156_, lean_object* v_h__5_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__3_splitter(v_n_150_, v_motive_151_, v_step_152_, v_h__1_153_, v_h__2_154_, v_h__3_155_, v_h__4_156_, v_h__5_157_);
lean_dec(v_n_150_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___redArg(lean_object* v_x_159_, lean_object* v_h__1_160_){
_start:
{
lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_163_; 
v_fst_161_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_fst_161_);
v_snd_162_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_snd_162_);
lean_dec_ref(v_x_159_);
v___x_163_ = lean_apply_2(v_h__1_160_, v_fst_161_, v_snd_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(lean_object* v_n_164_, lean_object* v_motive_165_, lean_object* v_x_166_, lean_object* v_h__1_167_){
_start:
{
lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_170_; 
v_fst_168_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v_x_166_);
v___x_170_ = lean_apply_2(v_h__1_167_, v_fst_168_, v_snd_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter___boxed(lean_object* v_n_171_, lean_object* v_motive_172_, lean_object* v_x_173_, lean_object* v_h__1_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker_0__Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go_match__1_splitter(v_n_171_, v_motive_172_, v_x_173_, v_h__1_174_);
lean_dec(v_n_171_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(lean_object* v_n_176_, lean_object* v_f_177_, lean_object* v_proof_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker_go(v_n_176_, v_f_177_, v_proof_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker___boxed(lean_object* v_n_181_, lean_object* v_f_182_, lean_object* v_proof_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Std_Tactic_BVDecide_LRAT_Internal_compactLratChecker(v_n_181_, v_f_182_, v_proof_183_);
lean_dec_ref(v_proof_183_);
lean_dec(v_n_181_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Instance(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_CompactLRATChecker(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
