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
uint8_t v_a_38__boxed_19_; lean_object* v_res_20_; 
v_a_38__boxed_19_ = lean_unbox(v_a_14_);
v_res_20_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_38__boxed_19_, v_h__1_15_, v_h__2_16_, v_h__3_17_, v_h__4_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(lean_object* v_motive_21_, uint8_t v_a_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_, lean_object* v_h__3_25_, lean_object* v_h__4_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___redArg(v_a_22_, v_h__1_23_, v_h__2_24_, v_h__3_25_, v_h__4_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter___boxed(lean_object* v_motive_28_, lean_object* v_a_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_, lean_object* v_h__4_33_){
_start:
{
uint8_t v_a_57__boxed_34_; lean_object* v_res_35_; 
v_a_57__boxed_34_ = lean_unbox(v_a_29_);
v_res_35_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_Assignment_instToString_match__1_splitter(v_motive_28_, v_a_57__boxed_34_, v_h__1_30_, v_h__2_31_, v_h__3_32_, v_h__4_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(lean_object* v_acc_36_, lean_object* v_h__1_37_, lean_object* v_h__2_38_, lean_object* v_h__3_39_, lean_object* v_h__4_40_){
_start:
{
switch(lean_obj_tag(v_acc_36_))
{
case 0:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
lean_dec(v_h__2_38_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_apply_1(v_h__1_37_, v___x_41_);
return v___x_42_;
}
case 1:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
lean_dec(v_h__4_40_);
lean_dec(v_h__3_39_);
lean_dec(v_h__1_37_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_apply_1(v_h__2_38_, v___x_43_);
return v___x_44_;
}
case 2:
{
lean_object* v_l_45_; lean_object* v___x_46_; 
lean_dec(v_h__4_40_);
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
v_l_45_ = lean_ctor_get(v_acc_36_, 0);
lean_inc_ref(v_l_45_);
lean_dec_ref(v_acc_36_);
v___x_46_ = lean_apply_1(v_h__3_39_, v_l_45_);
return v___x_46_;
}
default: 
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_dec(v_h__3_39_);
lean_dec(v_h__2_38_);
lean_dec(v_h__1_37_);
v___x_47_ = lean_box(0);
v___x_48_ = lean_apply_1(v_h__4_40_, v___x_47_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(lean_object* v_n_49_, lean_object* v_motive_50_, lean_object* v_acc_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_, lean_object* v_h__3_54_, lean_object* v_h__4_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___redArg(v_acc_51_, v_h__1_52_, v_h__2_53_, v_h__3_54_, v_h__4_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter___boxed(lean_object* v_n_57_, lean_object* v_motive_58_, lean_object* v_acc_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_, lean_object* v_h__3_62_, lean_object* v_h__4_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__3_splitter(v_n_57_, v_motive_58_, v_acc_59_, v_h__1_60_, v_h__2_61_, v_h__3_62_, v_h__4_63_);
lean_dec(v_n_57_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(uint8_t v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_, lean_object* v_h__3_68_, lean_object* v_h__4_69_){
_start:
{
switch(v_x_65_)
{
case 0:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_h__4_69_);
lean_dec(v_h__3_68_);
lean_dec(v_h__2_67_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_apply_1(v_h__1_66_, v___x_70_);
return v___x_71_;
}
case 1:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_h__4_69_);
lean_dec(v_h__3_68_);
lean_dec(v_h__1_66_);
v___x_72_ = lean_box(0);
v___x_73_ = lean_apply_1(v_h__2_67_, v___x_72_);
return v___x_73_;
}
case 2:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_h__4_69_);
lean_dec(v_h__2_67_);
lean_dec(v_h__1_66_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_h__3_68_, v___x_74_);
return v___x_75_;
}
default: 
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec(v_h__3_68_);
lean_dec(v_h__2_67_);
lean_dec(v_h__1_66_);
v___x_76_ = lean_box(0);
v___x_77_ = lean_apply_1(v_h__4_69_, v___x_76_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg___boxed(lean_object* v_x_78_, lean_object* v_h__1_79_, lean_object* v_h__2_80_, lean_object* v_h__3_81_, lean_object* v_h__4_82_){
_start:
{
uint8_t v_x_38__boxed_83_; lean_object* v_res_84_; 
v_x_38__boxed_83_ = lean_unbox(v_x_78_);
v_res_84_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_38__boxed_83_, v_h__1_79_, v_h__2_80_, v_h__3_81_, v_h__4_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(lean_object* v_motive_85_, uint8_t v_x_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_, lean_object* v_h__3_89_, lean_object* v_h__4_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___redArg(v_x_86_, v_h__1_87_, v_h__2_88_, v_h__3_89_, v_h__4_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter___boxed(lean_object* v_motive_92_, lean_object* v_x_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_, lean_object* v_h__4_97_){
_start:
{
uint8_t v_x_57__boxed_98_; lean_object* v_res_99_; 
v_x_57__boxed_98_ = lean_unbox(v_x_93_);
v_res_99_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce__fold__fn_match__1_splitter(v_motive_92_, v_x_57__boxed_98_, v_h__1_94_, v_h__2_95_, v_h__3_96_, v_h__4_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(lean_object* v_x_100_, lean_object* v_h__1_101_, lean_object* v_h__2_102_, lean_object* v_h__3_103_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_h__2_102_);
lean_dec(v_h__1_101_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v_h__3_103_, v___x_104_);
return v___x_105_;
}
else
{
lean_object* v_val_106_; 
lean_dec(v_h__3_103_);
v_val_106_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_val_106_);
lean_dec_ref(v_x_100_);
if (lean_obj_tag(v_val_106_) == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; 
lean_dec(v_h__1_101_);
v___x_107_ = lean_box(0);
v___x_108_ = lean_apply_1(v_h__2_102_, v___x_107_);
return v___x_108_;
}
else
{
lean_object* v_val_109_; lean_object* v___x_110_; 
lean_dec(v_h__2_102_);
v_val_109_ = lean_ctor_get(v_val_106_, 0);
lean_inc(v_val_109_);
lean_dec_ref(v_val_106_);
v___x_110_ = lean_apply_1(v_h__1_101_, v_val_109_);
return v___x_110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(lean_object* v_n_111_, lean_object* v_motive_112_, lean_object* v_x_113_, lean_object* v_h__1_114_, lean_object* v_h__2_115_, lean_object* v_h__3_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___redArg(v_x_113_, v_h__1_114_, v_h__2_115_, v_h__3_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter___boxed(lean_object* v_n_118_, lean_object* v_motive_119_, lean_object* v_x_120_, lean_object* v_h__1_121_, lean_object* v_h__2_122_, lean_object* v_h__3_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__3_splitter(v_n_118_, v_motive_119_, v_x_120_, v_h__1_121_, v_h__2_122_, v_h__3_123_);
lean_dec(v_n_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(lean_object* v_x_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_, lean_object* v_h__3_128_, lean_object* v_h__4_129_){
_start:
{
switch(lean_obj_tag(v_x_125_))
{
case 0:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_h__4_129_);
lean_dec(v_h__3_128_);
lean_dec(v_h__2_127_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_apply_1(v_h__1_126_, v___x_130_);
return v___x_131_;
}
case 1:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_h__4_129_);
lean_dec(v_h__3_128_);
lean_dec(v_h__1_126_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_apply_1(v_h__2_127_, v___x_132_);
return v___x_133_;
}
case 2:
{
lean_object* v_l_134_; lean_object* v_fst_135_; lean_object* v_snd_136_; lean_object* v___x_137_; 
lean_dec(v_h__4_129_);
lean_dec(v_h__2_127_);
lean_dec(v_h__1_126_);
v_l_134_ = lean_ctor_get(v_x_125_, 0);
lean_inc_ref(v_l_134_);
lean_dec_ref(v_x_125_);
v_fst_135_ = lean_ctor_get(v_l_134_, 0);
lean_inc(v_fst_135_);
v_snd_136_ = lean_ctor_get(v_l_134_, 1);
lean_inc(v_snd_136_);
lean_dec_ref(v_l_134_);
v___x_137_ = lean_apply_2(v_h__3_128_, v_fst_135_, v_snd_136_);
return v___x_137_;
}
default: 
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_h__3_128_);
lean_dec(v_h__2_127_);
lean_dec(v_h__1_126_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_apply_1(v_h__4_129_, v___x_138_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(lean_object* v_n_140_, lean_object* v_motive_141_, lean_object* v_x_142_, lean_object* v_h__1_143_, lean_object* v_h__2_144_, lean_object* v_h__3_145_, lean_object* v_h__4_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___redArg(v_x_142_, v_h__1_143_, v_h__2_144_, v_h__3_145_, v_h__4_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter___boxed(lean_object* v_n_148_, lean_object* v_motive_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_, lean_object* v_h__4_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Std_Tactic_BVDecide_LRAT_Internal_Formula_RupAddSound_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint_match__1_splitter(v_n_148_, v_motive_149_, v_x_150_, v_h__1_151_, v_h__2_152_, v_h__3_153_, v_h__4_154_);
lean_dec(v_n_148_);
return v_res_155_;
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
