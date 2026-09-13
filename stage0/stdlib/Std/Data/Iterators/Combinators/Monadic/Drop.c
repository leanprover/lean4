// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.Drop
// Imports: public import Init.Data.Iterators.Consumers.Loop
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_drop___redArg(lean_object* v_n_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_n_1_);
lean_ctor_set(v___x_3_, 1, v_it_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_drop(lean_object* v_00_u03b1_4_, lean_object* v_m_5_, lean_object* v_00_u03b2_6_, lean_object* v_n_7_, lean_object* v_it_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_n_7_);
lean_ctor_set(v___x_9_, 1, v_it_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0(lean_object* v_remaining_10_, lean_object* v_toPure_11_, lean_object* v_____do__lift_12_){
_start:
{
switch(lean_obj_tag(v_____do__lift_12_))
{
case 0:
{
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_30_; 
v_it_13_ = lean_ctor_get(v_____do__lift_12_, 0);
v_out_14_ = lean_ctor_get(v_____do__lift_12_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_____do__lift_12_);
if (v_isSharedCheck_30_ == 0)
{
v___x_16_ = v_____do__lift_12_;
v_isShared_17_ = v_isSharedCheck_30_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_out_14_);
lean_inc(v_it_13_);
lean_dec(v_____do__lift_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_30_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_zero_18_; uint8_t v_isZero_19_; 
v_zero_18_ = lean_unsigned_to_nat(0u);
v_isZero_19_ = lean_nat_dec_eq(v_remaining_10_, v_zero_18_);
if (v_isZero_19_ == 1)
{
lean_object* v___x_20_; lean_object* v___x_22_; 
lean_dec(v_remaining_10_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v_zero_18_);
lean_ctor_set(v___x_20_, 1, v_it_13_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_22_ = v___x_16_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_out_14_);
v___x_22_ = v_reuseFailAlloc_24_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_22_);
return v___x_23_;
}
}
else
{
lean_object* v_one_25_; lean_object* v_n_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_del_object(v___x_16_);
lean_dec(v_out_14_);
v_one_25_ = lean_unsigned_to_nat(1u);
v_n_26_ = lean_nat_sub(v_remaining_10_, v_one_25_);
lean_dec(v_remaining_10_);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v_n_26_);
lean_ctor_set(v___x_27_, 1, v_it_13_);
v___x_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
v___x_29_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_28_);
return v___x_29_;
}
}
}
case 1:
{
lean_object* v_it_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_40_; 
v_it_31_ = lean_ctor_get(v_____do__lift_12_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v_____do__lift_12_);
if (v_isSharedCheck_40_ == 0)
{
v___x_33_ = v_____do__lift_12_;
v_isShared_34_ = v_isSharedCheck_40_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_it_31_);
lean_dec(v_____do__lift_12_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_40_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v_remaining_10_);
lean_ctor_set(v___x_35_, 1, v_it_31_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_35_);
v___x_37_ = v___x_33_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_39_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; 
v___x_38_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_37_);
return v___x_38_;
}
}
}
default: 
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_remaining_10_);
v___x_41_ = lean_box(2);
v___x_42_ = lean_apply_2(v_toPure_11_, lean_box(0), v___x_41_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg___lam__1(lean_object* v_toPure_43_, lean_object* v_inst_44_, lean_object* v_toBind_45_, lean_object* v_it_46_){
_start:
{
lean_object* v_remaining_47_; lean_object* v_inner_48_; lean_object* v___f_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_remaining_47_ = lean_ctor_get(v_it_46_, 0);
lean_inc(v_remaining_47_);
v_inner_48_ = lean_ctor_get(v_it_46_, 1);
lean_inc(v_inner_48_);
lean_dec_ref(v_it_46_);
v___f_49_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0), 3, 2);
lean_closure_set(v___f_49_, 0, v_remaining_47_);
lean_closure_set(v___f_49_, 1, v_toPure_43_);
v___x_50_ = lean_apply_1(v_inst_44_, v_inner_48_);
v___x_51_ = lean_apply_4(v_toBind_45_, lean_box(0), lean_box(0), v___x_50_, v___f_49_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_toApplicative_54_; lean_object* v_toBind_55_; lean_object* v_toPure_56_; lean_object* v___f_57_; 
v_toApplicative_54_ = lean_ctor_get(v_inst_52_, 0);
lean_inc_ref(v_toApplicative_54_);
v_toBind_55_ = lean_ctor_get(v_inst_52_, 1);
lean_inc(v_toBind_55_);
lean_dec_ref(v_inst_52_);
v_toPure_56_ = lean_ctor_get(v_toApplicative_54_, 1);
lean_inc(v_toPure_56_);
lean_dec_ref(v_toApplicative_54_);
v___f_57_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_57_, 0, v_toPure_56_);
lean_closure_set(v___f_57_, 1, v_inst_53_);
lean_closure_set(v___f_57_, 2, v_toBind_55_);
return v___f_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIterator(lean_object* v_00_u03b1_58_, lean_object* v_m_59_, lean_object* v_00_u03b2_60_, lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Std_Iterators_Types_Drop_instIterator___redArg(v_inst_61_, v_inst_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation(lean_object* v_00_u03b1_68_, lean_object* v_m_69_, lean_object* v_00_u03b2_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation___boxed(lean_object* v_00_u03b1_75_, lean_object* v_m_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_inst_79_, lean_object* v_inst_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instFinitenessRelation(v_00_u03b1_75_, v_m_76_, v_00_u03b2_77_, v_inst_78_, v_inst_79_, v_inst_80_);
lean_dec_ref(v_inst_79_);
lean_dec(v_inst_78_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___redArg();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation(lean_object* v_00_u03b1_86_, lean_object* v_m_87_, lean_object* v_00_u03b2_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_box(0);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation___boxed(lean_object* v_00_u03b1_93_, lean_object* v_m_94_, lean_object* v_00_u03b2_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_inst_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Std_Data_Iterators_Combinators_Monadic_Drop_0__Std_Iterators_Types_Drop_instProductivenessRelation(v_00_u03b1_93_, v_m_94_, v_00_u03b2_95_, v_inst_96_, v_inst_97_, v_inst_98_);
lean_dec_ref(v_inst_97_);
lean_dec(v_inst_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_100_, lean_object* v_recur_101_, lean_object* v_it_102_, lean_object* v_____do__lift_103_){
_start:
{
if (lean_obj_tag(v_____do__lift_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
lean_dec_ref(v_it_102_);
lean_dec(v_recur_101_);
v_a_104_ = lean_ctor_get(v_____do__lift_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v_____do__lift_103_, 1);
v___x_105_ = lean_apply_2(v_toPure_100_, lean_box(0), v_a_104_);
return v___x_105_;
}
else
{
lean_object* v_a_106_; lean_object* v___x_107_; 
lean_dec(v_toPure_100_);
v_a_106_ = lean_ctor_get(v_____do__lift_103_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v_____do__lift_103_, 1);
v___x_107_ = lean_apply_4(v_recur_101_, v_it_102_, v_a_106_, lean_box(0), lean_box(0));
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_108_, lean_object* v_recur_109_, lean_object* v___y_110_, lean_object* v_acc_111_, lean_object* v_toBind_112_, lean_object* v_s_113_){
_start:
{
switch(lean_obj_tag(v_s_113_))
{
case 0:
{
lean_object* v_it_114_; lean_object* v_out_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_it_114_ = lean_ctor_get(v_s_113_, 0);
lean_inc(v_it_114_);
v_out_115_ = lean_ctor_get(v_s_113_, 1);
lean_inc(v_out_115_);
lean_dec_ref_known(v_s_113_, 2);
v___f_116_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_116_, 0, v_toPure_108_);
lean_closure_set(v___f_116_, 1, v_recur_109_);
lean_closure_set(v___f_116_, 2, v_it_114_);
v___x_117_ = lean_apply_3(v___y_110_, v_out_115_, lean_box(0), v_acc_111_);
v___x_118_ = lean_apply_4(v_toBind_112_, lean_box(0), lean_box(0), v___x_117_, v___f_116_);
return v___x_118_;
}
case 1:
{
lean_object* v_it_119_; lean_object* v___x_120_; 
lean_dec(v_toBind_112_);
lean_dec(v___y_110_);
lean_dec(v_toPure_108_);
v_it_119_ = lean_ctor_get(v_s_113_, 0);
lean_inc(v_it_119_);
lean_dec_ref_known(v_s_113_, 1);
v___x_120_ = lean_apply_4(v_recur_109_, v_it_119_, v_acc_111_, lean_box(0), lean_box(0));
return v___x_120_;
}
default: 
{
lean_object* v___x_121_; 
lean_dec(v_toBind_112_);
lean_dec(v___y_110_);
lean_dec(v_recur_109_);
v___x_121_ = lean_apply_2(v_toPure_108_, lean_box(0), v_acc_111_);
return v___x_121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__3(lean_object* v_inst_122_, lean_object* v_toPure_123_, lean_object* v___y_124_, lean_object* v_toBind_125_, lean_object* v_inst_126_, lean_object* v_lift_127_, lean_object* v_it_128_, lean_object* v_acc_129_, lean_object* v_hP_130_, lean_object* v_recur_131_){
_start:
{
lean_object* v_toApplicative_132_; lean_object* v_toBind_133_; lean_object* v_toPure_134_; lean_object* v_remaining_135_; lean_object* v_inner_136_; lean_object* v___f_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_toApplicative_132_ = lean_ctor_get(v_inst_122_, 0);
lean_inc_ref(v_toApplicative_132_);
v_toBind_133_ = lean_ctor_get(v_inst_122_, 1);
lean_inc(v_toBind_133_);
lean_dec_ref(v_inst_122_);
v_toPure_134_ = lean_ctor_get(v_toApplicative_132_, 1);
lean_inc(v_toPure_134_);
lean_dec_ref(v_toApplicative_132_);
v_remaining_135_ = lean_ctor_get(v_it_128_, 0);
lean_inc(v_remaining_135_);
v_inner_136_ = lean_ctor_get(v_it_128_, 1);
lean_inc(v_inner_136_);
lean_dec_ref(v_it_128_);
v___f_137_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_137_, 0, v_toPure_123_);
lean_closure_set(v___f_137_, 1, v_recur_131_);
lean_closure_set(v___f_137_, 2, v___y_124_);
lean_closure_set(v___f_137_, 3, v_acc_129_);
lean_closure_set(v___f_137_, 4, v_toBind_125_);
v___f_138_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIterator___redArg___lam__0), 3, 2);
lean_closure_set(v___f_138_, 0, v_remaining_135_);
lean_closure_set(v___f_138_, 1, v_toPure_134_);
v___x_139_ = lean_apply_1(v_inst_126_, v_inner_136_);
v___x_140_ = lean_apply_4(v_toBind_133_, lean_box(0), lean_box(0), v___x_139_, v___f_138_);
v___x_141_ = lean_apply_4(v_lift_127_, lean_box(0), lean_box(0), v___f_137_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2(lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_lift_145_, lean_object* v_00_u03b3_146_, lean_object* v_Pl_147_, lean_object* v_it_148_, lean_object* v_init_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_toApplicative_151_; lean_object* v_toBind_152_; lean_object* v_toPure_153_; lean_object* v___f_154_; lean_object* v___x_155_; 
v_toApplicative_151_ = lean_ctor_get(v_inst_142_, 0);
lean_inc_ref(v_toApplicative_151_);
v_toBind_152_ = lean_ctor_get(v_inst_142_, 1);
lean_inc(v_toBind_152_);
lean_dec_ref(v_inst_142_);
v_toPure_153_ = lean_ctor_get(v_toApplicative_151_, 1);
lean_inc(v_toPure_153_);
lean_dec_ref(v_toApplicative_151_);
v___f_154_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_154_, 0, v_inst_143_);
lean_closure_set(v___f_154_, 1, v_toPure_153_);
lean_closure_set(v___f_154_, 2, v___y_150_);
lean_closure_set(v___f_154_, 3, v_toBind_152_);
lean_closure_set(v___f_154_, 4, v_inst_144_);
lean_closure_set(v___f_154_, 5, v_lift_145_);
v___x_155_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_154_, v_it_148_, v_init_149_, lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop___redArg(lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_inst_158_){
_start:
{
lean_object* v___f_159_; 
v___f_159_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_159_, 0, v_inst_157_);
lean_closure_set(v___f_159_, 1, v_inst_156_);
lean_closure_set(v___f_159_, 2, v_inst_158_);
return v___f_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Drop_instIteratorLoop(lean_object* v_00_u03b1_160_, lean_object* v_m_161_, lean_object* v_00_u03b2_162_, lean_object* v_n_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_inst_166_){
_start:
{
lean_object* v___f_167_; 
v___f_167_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Drop_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_167_, 0, v_inst_165_);
lean_closure_set(v___f_167_, 1, v_inst_164_);
lean_closure_set(v___f_167_, 2, v_inst_166_);
return v___f_167_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_Drop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
}
#ifdef __cplusplus
}
#endif
