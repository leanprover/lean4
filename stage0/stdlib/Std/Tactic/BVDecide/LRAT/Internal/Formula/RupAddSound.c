// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddSound
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult import Init.ByCases import Init.Data.Array.Bootstrap import Init.Data.Int.OfNat import Init.Data.Nat.Linear import Init.Data.Nat.Simproc
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(uint8_t v_a_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_, lean_object* v_h__4_5_){
_start:
{
switch(v_a_1_)
{
case 0:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
case 1:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_apply_1(v_h__2_3_, v___x_8_);
return v___x_9_;
}
case 2:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_h__4_5_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_apply_1(v_h__3_4_, v___x_10_);
return v___x_11_;
}
default: 
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_12_ = lean_box(0);
v___x_13_ = lean_apply_1(v_h__4_5_, v___x_12_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg___boxed(lean_object* v_a_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_, lean_object* v_h__3_17_, lean_object* v_h__4_18_){
_start:
{
uint8_t v_a_46__boxed_19_; lean_object* v_res_20_; 
v_a_46__boxed_19_ = lean_unbox(v_a_14_);
v_res_20_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_46__boxed_19_, v_h__1_15_, v_h__2_16_, v_h__3_17_, v_h__4_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object* v_motive_21_, uint8_t v_a_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_, lean_object* v_h__4_26_){
_start:
{
switch(v_a_22_)
{
case 0:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_apply_1(v_h__1_23_, v___x_27_);
return v___x_28_;
}
case 1:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__3_25_);
lean_dec(v_h__1_23_);
v___x_29_ = lean_box(0);
v___x_30_ = lean_apply_1(v_h__2_24_, v___x_29_);
return v___x_30_;
}
case 2:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__4_26_);
lean_dec(v_h__2_24_);
lean_dec(v_h__1_23_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__3_25_, v___x_31_);
return v___x_32_;
}
default: 
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_25_);
lean_dec(v_h__2_24_);
lean_dec(v_h__1_23_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__4_26_, v___x_33_);
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object* v_motive_35_, lean_object* v_a_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_, lean_object* v_h__3_39_, lean_object* v_h__4_40_){
_start:
{
uint8_t v_a_65__boxed_41_; lean_object* v_res_42_; 
v_a_65__boxed_41_ = lean_unbox(v_a_36_);
v_res_42_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_35_, v_a_65__boxed_41_, v_h__1_37_, v_h__2_38_, v_h__3_39_, v_h__4_40_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(lean_object* v_acc_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_, lean_object* v_h__4_47_){
_start:
{
switch(lean_obj_tag(v_acc_43_))
{
case 0:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_44_, v___x_48_);
return v___x_49_;
}
case 1:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v___x_50_ = lean_box(0);
v___x_51_ = lean_apply_1(v_h__2_45_, v___x_50_);
return v___x_51_;
}
case 2:
{
lean_object* v_l_52_; lean_object* v___x_53_; 
lean_dec(v_h__4_47_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v_l_52_ = lean_ctor_get(v_acc_43_, 0);
lean_inc_ref(v_l_52_);
lean_dec_ref(v_acc_43_);
v___x_53_ = lean_apply_1(v_h__3_46_, v_l_52_);
return v___x_53_;
}
default: 
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__4_47_, v___x_54_);
return v___x_55_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(lean_object* v_n_56_, lean_object* v_motive_57_, lean_object* v_acc_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_, lean_object* v_h__3_61_, lean_object* v_h__4_62_){
_start:
{
switch(lean_obj_tag(v_acc_58_))
{
case 0:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_h__4_62_);
lean_dec(v_h__3_61_);
lean_dec(v_h__2_60_);
v___x_63_ = lean_box(0);
v___x_64_ = lean_apply_1(v_h__1_59_, v___x_63_);
return v___x_64_;
}
case 1:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec(v_h__4_62_);
lean_dec(v_h__3_61_);
lean_dec(v_h__1_59_);
v___x_65_ = lean_box(0);
v___x_66_ = lean_apply_1(v_h__2_60_, v___x_65_);
return v___x_66_;
}
case 2:
{
lean_object* v_l_67_; lean_object* v___x_68_; 
lean_dec(v_h__4_62_);
lean_dec(v_h__2_60_);
lean_dec(v_h__1_59_);
v_l_67_ = lean_ctor_get(v_acc_58_, 0);
lean_inc_ref(v_l_67_);
lean_dec_ref(v_acc_58_);
v___x_68_ = lean_apply_1(v_h__3_61_, v_l_67_);
return v___x_68_;
}
default: 
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_h__3_61_);
lean_dec(v_h__2_60_);
lean_dec(v_h__1_59_);
v___x_69_ = lean_box(0);
v___x_70_ = lean_apply_1(v_h__4_62_, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(lean_object* v_n_71_, lean_object* v_motive_72_, lean_object* v_acc_73_, lean_object* v_h__1_74_, lean_object* v_h__2_75_, lean_object* v_h__3_76_, lean_object* v_h__4_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(v_n_71_, v_motive_72_, v_acc_73_, v_h__1_74_, v_h__2_75_, v_h__3_76_, v_h__4_77_);
lean_dec(v_n_71_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(uint8_t v_x_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_, lean_object* v_h__3_82_, lean_object* v_h__4_83_){
_start:
{
switch(v_x_79_)
{
case 0:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_h__4_83_);
lean_dec(v_h__3_82_);
lean_dec(v_h__2_81_);
v___x_84_ = lean_box(0);
v___x_85_ = lean_apply_1(v_h__1_80_, v___x_84_);
return v___x_85_;
}
case 1:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v_h__4_83_);
lean_dec(v_h__3_82_);
lean_dec(v_h__1_80_);
v___x_86_ = lean_box(0);
v___x_87_ = lean_apply_1(v_h__2_81_, v___x_86_);
return v___x_87_;
}
case 2:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_dec(v_h__4_83_);
lean_dec(v_h__2_81_);
lean_dec(v_h__1_80_);
v___x_88_ = lean_box(0);
v___x_89_ = lean_apply_1(v_h__3_82_, v___x_88_);
return v___x_89_;
}
default: 
{
lean_object* v___x_90_; lean_object* v___x_91_; 
lean_dec(v_h__3_82_);
lean_dec(v_h__2_81_);
lean_dec(v_h__1_80_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_apply_1(v_h__4_83_, v___x_90_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(lean_object* v_x_92_, lean_object* v_h__1_93_, lean_object* v_h__2_94_, lean_object* v_h__3_95_, lean_object* v_h__4_96_){
_start:
{
uint8_t v_x_46__boxed_97_; lean_object* v_res_98_; 
v_x_46__boxed_97_ = lean_unbox(v_x_92_);
v_res_98_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_46__boxed_97_, v_h__1_93_, v_h__2_94_, v_h__3_95_, v_h__4_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(lean_object* v_motive_99_, uint8_t v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_, lean_object* v_h__4_104_){
_start:
{
switch(v_x_100_)
{
case 0:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_h__4_104_);
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
v___x_105_ = lean_box(0);
v___x_106_ = lean_apply_1(v_h__1_101_, v___x_105_);
return v___x_106_;
}
case 1:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_h__4_104_);
lean_dec(v_h__3_103_);
lean_dec(v_h__1_101_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_1(v_h__2_102_, v___x_107_);
return v___x_108_;
}
case 2:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_h__4_104_);
lean_dec(v_h__2_102_);
lean_dec(v_h__1_101_);
v___x_109_ = lean_box(0);
v___x_110_ = lean_apply_1(v_h__3_103_, v___x_109_);
return v___x_110_;
}
default: 
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_h__3_103_);
lean_dec(v_h__2_102_);
lean_dec(v_h__1_101_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_apply_1(v_h__4_104_, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(lean_object* v_motive_113_, lean_object* v_x_114_, lean_object* v_h__1_115_, lean_object* v_h__2_116_, lean_object* v_h__3_117_, lean_object* v_h__4_118_){
_start:
{
uint8_t v_x_65__boxed_119_; lean_object* v_res_120_; 
v_x_65__boxed_119_ = lean_unbox(v_x_114_);
v_res_120_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(v_motive_113_, v_x_65__boxed_119_, v_h__1_115_, v_h__2_116_, v_h__3_117_, v_h__4_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object* v_x_121_, lean_object* v_h__1_122_, lean_object* v_h__2_123_, lean_object* v_h__3_124_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v_h__2_123_);
lean_dec(v_h__1_122_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_apply_1(v_h__3_124_, v___x_125_);
return v___x_126_;
}
else
{
lean_object* v_val_127_; 
lean_dec(v_h__3_124_);
v_val_127_ = lean_ctor_get(v_x_121_, 0);
lean_inc(v_val_127_);
lean_dec_ref(v_x_121_);
if (lean_obj_tag(v_val_127_) == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_h__1_122_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_apply_1(v_h__2_123_, v___x_128_);
return v___x_129_;
}
else
{
lean_object* v_val_130_; lean_object* v___x_131_; 
lean_dec(v_h__2_123_);
v_val_130_ = lean_ctor_get(v_val_127_, 0);
lean_inc(v_val_130_);
lean_dec_ref(v_val_127_);
v___x_131_ = lean_apply_1(v_h__1_122_, v_val_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object* v_n_132_, lean_object* v_motive_133_, lean_object* v_x_134_, lean_object* v_h__1_135_, lean_object* v_h__2_136_, lean_object* v_h__3_137_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__2_136_);
lean_dec(v_h__1_135_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__3_137_, v___x_138_);
return v___x_139_;
}
else
{
lean_object* v_val_140_; 
lean_dec(v_h__3_137_);
v_val_140_ = lean_ctor_get(v_x_134_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_x_134_);
if (lean_obj_tag(v_val_140_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_h__1_135_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_h__2_136_, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
lean_dec(v_h__2_136_);
v_val_143_ = lean_ctor_get(v_val_140_, 0);
lean_inc(v_val_143_);
lean_dec_ref(v_val_140_);
v___x_144_ = lean_apply_1(v_h__1_135_, v_val_143_);
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object* v_n_145_, lean_object* v_motive_146_, lean_object* v_x_147_, lean_object* v_h__1_148_, lean_object* v_h__2_149_, lean_object* v_h__3_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_145_, v_motive_146_, v_x_147_, v_h__1_148_, v_h__2_149_, v_h__3_150_);
lean_dec(v_n_145_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object* v_x_152_, lean_object* v_h__1_153_, lean_object* v_h__2_154_, lean_object* v_h__3_155_, lean_object* v_h__4_156_){
_start:
{
switch(lean_obj_tag(v_x_152_))
{
case 0:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_h__4_156_);
lean_dec(v_h__3_155_);
lean_dec(v_h__2_154_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_1(v_h__1_153_, v___x_157_);
return v___x_158_;
}
case 1:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v_h__4_156_);
lean_dec(v_h__3_155_);
lean_dec(v_h__1_153_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_1(v_h__2_154_, v___x_159_);
return v___x_160_;
}
case 2:
{
lean_object* v_l_161_; lean_object* v_fst_162_; lean_object* v_snd_163_; lean_object* v___x_164_; 
lean_dec(v_h__4_156_);
lean_dec(v_h__2_154_);
lean_dec(v_h__1_153_);
v_l_161_ = lean_ctor_get(v_x_152_, 0);
lean_inc_ref(v_l_161_);
lean_dec_ref(v_x_152_);
v_fst_162_ = lean_ctor_get(v_l_161_, 0);
lean_inc(v_fst_162_);
v_snd_163_ = lean_ctor_get(v_l_161_, 1);
lean_inc(v_snd_163_);
lean_dec_ref(v_l_161_);
v___x_164_ = lean_apply_2(v_h__3_155_, v_fst_162_, v_snd_163_);
return v___x_164_;
}
default: 
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v_h__3_155_);
lean_dec(v_h__2_154_);
lean_dec(v_h__1_153_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_1(v_h__4_156_, v___x_165_);
return v___x_166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object* v_n_167_, lean_object* v_motive_168_, lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_, lean_object* v_h__3_172_, lean_object* v_h__4_173_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
v___x_174_ = lean_box(0);
v___x_175_ = lean_apply_1(v_h__1_170_, v___x_174_);
return v___x_175_;
}
case 1:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec(v_h__4_173_);
lean_dec(v_h__3_172_);
lean_dec(v_h__1_170_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_apply_1(v_h__2_171_, v___x_176_);
return v___x_177_;
}
case 2:
{
lean_object* v_l_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_181_; 
lean_dec(v_h__4_173_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v_l_178_ = lean_ctor_get(v_x_169_, 0);
lean_inc_ref(v_l_178_);
lean_dec_ref(v_x_169_);
v_fst_179_ = lean_ctor_get(v_l_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v_l_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v_l_178_);
v___x_181_ = lean_apply_2(v_h__3_172_, v_fst_179_, v_snd_180_);
return v___x_181_;
}
default: 
{
lean_object* v___x_182_; lean_object* v___x_183_; 
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v___x_182_ = lean_box(0);
v___x_183_ = lean_apply_1(v_h__4_173_, v___x_182_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object* v_n_184_, lean_object* v_motive_185_, lean_object* v_x_186_, lean_object* v_h__1_187_, lean_object* v_h__2_188_, lean_object* v_h__3_189_, lean_object* v_h__4_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_184_, v_motive_185_, v_x_186_, v_h__1_187_, v_h__2_188_, v_h__3_189_, v_h__4_190_);
lean_dec(v_n_184_);
return v_res_191_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound(builtin);
}
#ifdef __cplusplus
}
#endif
