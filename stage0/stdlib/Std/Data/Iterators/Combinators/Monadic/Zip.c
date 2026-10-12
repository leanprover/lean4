// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic.Zip
// Imports: public import Init.Data.Option.Lemmas public import Init.Data.Iterators.Consumers.Loop
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_zip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_zip___redArg(lean_object* v_left_1_, lean_object* v_right_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4_, 0, v_left_1_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
lean_ctor_set(v___x_4_, 2, v_right_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_zip(lean_object* v_m_5_, lean_object* v_00_u03b1_u2081_6_, lean_object* v_00_u03b2_u2081_7_, lean_object* v_inst_8_, lean_object* v_00_u03b1_u2082_9_, lean_object* v_00_u03b2_u2082_10_, lean_object* v_left_11_, lean_object* v_right_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v_left_11_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
lean_ctor_set(v___x_14_, 2, v_right_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_zip___boxed(lean_object* v_m_15_, lean_object* v_00_u03b1_u2081_16_, lean_object* v_00_u03b2_u2081_17_, lean_object* v_inst_18_, lean_object* v_00_u03b1_u2082_19_, lean_object* v_00_u03b2_u2082_20_, lean_object* v_left_21_, lean_object* v_right_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_IterM_zip(v_m_15_, v_00_u03b1_u2081_16_, v_00_u03b2_u2081_17_, v_inst_18_, v_00_u03b1_u2082_19_, v_00_u03b2_u2082_20_, v_left_21_, v_right_22_);
lean_dec(v_inst_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0(lean_object* v_right_24_, lean_object* v_toPure_25_, lean_object* v_memoizedLeft_26_, lean_object* v_____do__lift_27_){
_start:
{
switch(lean_obj_tag(v_____do__lift_27_))
{
case 0:
{
lean_object* v_it_28_; lean_object* v_out_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v_memoizedLeft_26_);
v_it_28_ = lean_ctor_get(v_____do__lift_27_, 0);
lean_inc(v_it_28_);
v_out_29_ = lean_ctor_get(v_____do__lift_27_, 1);
lean_inc(v_out_29_);
lean_dec_ref_known(v_____do__lift_27_, 2);
v___x_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_30_, 0, v_out_29_);
v___x_31_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_31_, 0, v_it_28_);
lean_ctor_set(v___x_31_, 1, v___x_30_);
lean_ctor_set(v___x_31_, 2, v_right_24_);
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
v___x_33_ = lean_apply_2(v_toPure_25_, lean_box(0), v___x_32_);
return v___x_33_;
}
case 1:
{
lean_object* v_it_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_43_; 
v_it_34_ = lean_ctor_get(v_____do__lift_27_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_____do__lift_27_);
if (v_isSharedCheck_43_ == 0)
{
v___x_36_ = v_____do__lift_27_;
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_it_34_);
lean_dec(v_____do__lift_27_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v_it_34_);
lean_ctor_set(v___x_38_, 1, v_memoizedLeft_26_);
lean_ctor_set(v___x_38_, 2, v_right_24_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_38_);
v___x_40_ = v___x_36_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_38_);
v___x_40_ = v_reuseFailAlloc_42_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; 
v___x_41_ = lean_apply_2(v_toPure_25_, lean_box(0), v___x_40_);
return v___x_41_;
}
}
}
default: 
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_memoizedLeft_26_);
lean_dec(v_right_24_);
v___x_44_ = lean_box(2);
v___x_45_ = lean_apply_2(v_toPure_25_, lean_box(0), v___x_44_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1(lean_object* v_left_46_, lean_object* v_val_47_, lean_object* v_toPure_48_, lean_object* v_memoizedLeft_49_, lean_object* v_____do__lift_50_){
_start:
{
switch(lean_obj_tag(v_____do__lift_50_))
{
case 0:
{
lean_object* v_it_51_; lean_object* v_out_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_63_; 
lean_dec(v_memoizedLeft_49_);
v_it_51_ = lean_ctor_get(v_____do__lift_50_, 0);
v_out_52_ = lean_ctor_get(v_____do__lift_50_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_____do__lift_50_);
if (v_isSharedCheck_63_ == 0)
{
v___x_54_ = v_____do__lift_50_;
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_out_52_);
lean_inc(v_it_51_);
lean_dec(v_____do__lift_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_63_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_57_, 0, v_left_46_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
lean_ctor_set(v___x_57_, 2, v_it_51_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_val_47_);
lean_ctor_set(v___x_58_, 1, v_out_52_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 1, v___x_58_);
lean_ctor_set(v___x_54_, 0, v___x_57_);
v___x_60_ = v___x_54_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_62_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
lean_object* v___x_61_; 
v___x_61_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_60_);
return v___x_61_;
}
}
}
case 1:
{
lean_object* v_it_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_73_; 
lean_dec(v_val_47_);
v_it_64_ = lean_ctor_get(v_____do__lift_50_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_____do__lift_50_);
if (v_isSharedCheck_73_ == 0)
{
v___x_66_ = v_____do__lift_50_;
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_it_64_);
lean_dec(v_____do__lift_50_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_73_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_68_, 0, v_left_46_);
lean_ctor_set(v___x_68_, 1, v_memoizedLeft_49_);
lean_ctor_set(v___x_68_, 2, v_it_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_68_);
v___x_70_ = v___x_66_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_72_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
lean_object* v___x_71_; 
v___x_71_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_70_);
return v___x_71_;
}
}
}
default: 
{
lean_object* v___x_74_; lean_object* v___x_75_; 
lean_dec(v_memoizedLeft_49_);
lean_dec(v_val_47_);
lean_dec(v_left_46_);
v___x_74_ = lean_box(2);
v___x_75_ = lean_apply_2(v_toPure_48_, lean_box(0), v___x_74_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2(lean_object* v_toPure_76_, lean_object* v_inst_77_, lean_object* v_toBind_78_, lean_object* v_inst_79_, lean_object* v_it_80_){
_start:
{
lean_object* v_memoizedLeft_81_; 
v_memoizedLeft_81_ = lean_ctor_get(v_it_80_, 1);
lean_inc(v_memoizedLeft_81_);
if (lean_obj_tag(v_memoizedLeft_81_) == 0)
{
lean_object* v_left_82_; lean_object* v_right_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
lean_dec(v_inst_79_);
v_left_82_ = lean_ctor_get(v_it_80_, 0);
lean_inc(v_left_82_);
v_right_83_ = lean_ctor_get(v_it_80_, 2);
lean_inc(v_right_83_);
lean_dec_ref(v_it_80_);
v___f_84_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0), 4, 3);
lean_closure_set(v___f_84_, 0, v_right_83_);
lean_closure_set(v___f_84_, 1, v_toPure_76_);
lean_closure_set(v___f_84_, 2, v_memoizedLeft_81_);
v___x_85_ = lean_apply_1(v_inst_77_, v_left_82_);
v___x_86_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_85_, v___f_84_);
return v___x_86_;
}
else
{
lean_object* v_left_87_; lean_object* v_right_88_; lean_object* v_val_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_inst_77_);
v_left_87_ = lean_ctor_get(v_it_80_, 0);
lean_inc(v_left_87_);
v_right_88_ = lean_ctor_get(v_it_80_, 2);
lean_inc(v_right_88_);
lean_dec_ref(v_it_80_);
v_val_89_ = lean_ctor_get(v_memoizedLeft_81_, 0);
lean_inc(v_val_89_);
v___f_90_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1), 5, 4);
lean_closure_set(v___f_90_, 0, v_left_87_);
lean_closure_set(v___f_90_, 1, v_val_89_);
lean_closure_set(v___f_90_, 2, v_toPure_76_);
lean_closure_set(v___f_90_, 3, v_memoizedLeft_81_);
v___x_91_ = lean_apply_1(v_inst_79_, v_right_88_);
v___x_92_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_91_, v___f_90_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator___redArg(lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_inst_95_){
_start:
{
lean_object* v_toApplicative_96_; lean_object* v_toBind_97_; lean_object* v_toPure_98_; lean_object* v___f_99_; 
v_toApplicative_96_ = lean_ctor_get(v_inst_95_, 0);
lean_inc_ref(v_toApplicative_96_);
v_toBind_97_ = lean_ctor_get(v_inst_95_, 1);
lean_inc(v_toBind_97_);
lean_dec_ref(v_inst_95_);
v_toPure_98_ = lean_ctor_get(v_toApplicative_96_, 1);
lean_inc(v_toPure_98_);
lean_dec_ref(v_toApplicative_96_);
v___f_99_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_99_, 0, v_toPure_98_);
lean_closure_set(v___f_99_, 1, v_inst_93_);
lean_closure_set(v___f_99_, 2, v_toBind_97_);
lean_closure_set(v___f_99_, 3, v_inst_94_);
return v___f_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIterator(lean_object* v_m_100_, lean_object* v_00_u03b1_u2081_101_, lean_object* v_00_u03b2_u2081_102_, lean_object* v_inst_103_, lean_object* v_00_u03b1_u2082_104_, lean_object* v_00_u03b2_u2082_105_, lean_object* v_inst_106_, lean_object* v_inst_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Std_Iterators_Types_Zip_instIterator___redArg(v_inst_103_, v_inst_106_, v_inst_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_lt_match__1_splitter___redArg(lean_object* v_x_109_, lean_object* v_x_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_){
_start:
{
if (lean_obj_tag(v_x_109_) == 0)
{
lean_dec(v_h__2_112_);
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_val_114_; lean_object* v___x_115_; 
lean_dec(v_h__3_113_);
v_val_114_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v_x_110_, 1);
v___x_115_ = lean_apply_1(v_h__1_111_, v_val_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; 
lean_dec(v_h__1_111_);
v___x_116_ = lean_apply_4(v_h__3_113_, v_x_109_, v_x_110_, lean_box(0), lean_box(0));
return v___x_116_;
}
}
else
{
lean_dec(v_h__1_111_);
if (lean_obj_tag(v_x_110_) == 1)
{
lean_object* v_val_117_; lean_object* v_val_118_; lean_object* v___x_119_; 
lean_dec(v_h__3_113_);
v_val_117_ = lean_ctor_get(v_x_109_, 0);
lean_inc(v_val_117_);
lean_dec_ref_known(v_x_109_, 1);
v_val_118_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v_x_110_, 1);
v___x_119_ = lean_apply_2(v_h__2_112_, v_val_117_, v_val_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
lean_dec(v_h__2_112_);
v___x_120_ = lean_apply_4(v_h__3_113_, v_x_109_, v_x_110_, lean_box(0), lean_box(0));
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_lt_match__1_splitter(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_motive_123_, lean_object* v_x_124_, lean_object* v_x_125_, lean_object* v_h__1_126_, lean_object* v_h__2_127_, lean_object* v_h__3_128_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
lean_dec(v_h__2_127_);
if (lean_obj_tag(v_x_125_) == 1)
{
lean_object* v_val_129_; lean_object* v___x_130_; 
lean_dec(v_h__3_128_);
v_val_129_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_val_129_);
lean_dec_ref_known(v_x_125_, 1);
v___x_130_ = lean_apply_1(v_h__1_126_, v_val_129_);
return v___x_130_;
}
else
{
lean_object* v___x_131_; 
lean_dec(v_h__1_126_);
v___x_131_ = lean_apply_4(v_h__3_128_, v_x_124_, v_x_125_, lean_box(0), lean_box(0));
return v___x_131_;
}
}
else
{
lean_dec(v_h__1_126_);
if (lean_obj_tag(v_x_125_) == 1)
{
lean_object* v_val_132_; lean_object* v_val_133_; lean_object* v___x_134_; 
lean_dec(v_h__3_128_);
v_val_132_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_val_132_);
lean_dec_ref_known(v_x_124_, 1);
v_val_133_ = lean_ctor_get(v_x_125_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v_x_125_, 1);
v___x_134_ = lean_apply_2(v_h__2_127_, v_val_132_, v_val_133_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; 
lean_dec(v_h__2_127_);
v___x_135_ = lean_apply_4(v_h__3_128_, v_x_124_, v_x_125_, lean_box(0), lean_box(0));
return v___x_135_;
}
}
}
}
lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg(){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
}
LEAN_EXPORT void l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_138_;
v_res_138_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg();
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg___boxed(lean_object* v___dummy_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object* v_m_141_, lean_object* v_00_u03b1_u2081_142_, lean_object* v_00_u03b2_u2081_143_, lean_object* v_inst_144_, lean_object* v_00_u03b1_u2082_145_, lean_object* v_00_u03b2_u2082_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_box(0);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object* v_m_152_, lean_object* v_00_u03b1_u2081_153_, lean_object* v_00_u03b2_u2081_154_, lean_object* v_inst_155_, lean_object* v_00_u03b1_u2082_156_, lean_object* v_00_u03b2_u2082_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(v_m_152_, v_00_u03b1_u2081_153_, v_00_u03b2_u2081_154_, v_inst_155_, v_00_u03b1_u2082_156_, v_00_u03b2_u2082_157_, v_inst_158_, v_inst_159_, v_inst_160_, v_inst_161_);
lean_dec_ref(v_inst_159_);
lean_dec(v_inst_158_);
lean_dec(v_inst_155_);
return v_res_162_;
}
}
lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg(){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = lean_box(0);
return v___x_164_;
}
}
LEAN_EXPORT void l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_165_;
v_res_165_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg();
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg___boxed(lean_object* v___dummy_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg();
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(lean_object* v_m_168_, lean_object* v_00_u03b1_u2081_169_, lean_object* v_00_u03b2_u2081_170_, lean_object* v_inst_171_, lean_object* v_00_u03b1_u2082_172_, lean_object* v_00_u03b2_u2082_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(lean_object* v_m_179_, lean_object* v_00_u03b1_u2081_180_, lean_object* v_00_u03b2_u2081_181_, lean_object* v_inst_182_, lean_object* v_00_u03b1_u2082_183_, lean_object* v_00_u03b2_u2082_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(v_m_179_, v_00_u03b1_u2081_180_, v_00_u03b2_u2081_181_, v_inst_182_, v_00_u03b1_u2082_183_, v_00_u03b2_u2082_184_, v_inst_185_, v_inst_186_, v_inst_187_, v_inst_188_);
lean_dec_ref(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec(v_inst_182_);
return v_res_189_;
}
}
lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT void l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_192_;
v_res_192_ = l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg();
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation(lean_object* v_m_195_, lean_object* v_00_u03b1_u2081_196_, lean_object* v_00_u03b2_u2081_197_, lean_object* v_inst_198_, lean_object* v_00_u03b1_u2082_199_, lean_object* v_00_u03b2_u2082_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(lean_object* v_m_206_, lean_object* v_00_u03b1_u2081_207_, lean_object* v_00_u03b2_u2081_208_, lean_object* v_inst_209_, lean_object* v_00_u03b1_u2082_210_, lean_object* v_00_u03b2_u2082_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_Iterators_Types_Zip_instProductivenessRelation(v_m_206_, v_00_u03b1_u2081_207_, v_00_u03b2_u2081_208_, v_inst_209_, v_00_u03b1_u2082_210_, v_00_u03b2_u2082_211_, v_inst_212_, v_inst_213_, v_inst_214_, v_inst_215_);
lean_dec_ref(v_inst_213_);
lean_dec(v_inst_212_);
lean_dec(v_inst_209_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_217_, lean_object* v_recur_218_, lean_object* v_it_219_, lean_object* v_____do__lift_220_){
_start:
{
if (lean_obj_tag(v_____do__lift_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
lean_dec_ref(v_it_219_);
lean_dec(v_recur_218_);
v_a_221_ = lean_ctor_get(v_____do__lift_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v_____do__lift_220_, 1);
v___x_222_ = lean_apply_2(v_toPure_217_, lean_box(0), v_a_221_);
return v___x_222_;
}
else
{
lean_object* v_a_223_; lean_object* v___x_224_; 
lean_dec(v_toPure_217_);
v_a_223_ = lean_ctor_get(v_____do__lift_220_, 0);
lean_inc(v_a_223_);
lean_dec_ref_known(v_____do__lift_220_, 1);
v___x_224_ = lean_apply_4(v_recur_218_, v_it_219_, v_a_223_, lean_box(0), lean_box(0));
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_225_, lean_object* v_recur_226_, lean_object* v___y_227_, lean_object* v_acc_228_, lean_object* v_toBind_229_, lean_object* v_s_230_){
_start:
{
switch(lean_obj_tag(v_s_230_))
{
case 0:
{
lean_object* v_it_231_; lean_object* v_out_232_; lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_it_231_ = lean_ctor_get(v_s_230_, 0);
lean_inc(v_it_231_);
v_out_232_ = lean_ctor_get(v_s_230_, 1);
lean_inc(v_out_232_);
lean_dec_ref_known(v_s_230_, 2);
v___f_233_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_233_, 0, v_toPure_225_);
lean_closure_set(v___f_233_, 1, v_recur_226_);
lean_closure_set(v___f_233_, 2, v_it_231_);
v___x_234_ = lean_apply_3(v___y_227_, v_out_232_, lean_box(0), v_acc_228_);
v___x_235_ = lean_apply_4(v_toBind_229_, lean_box(0), lean_box(0), v___x_234_, v___f_233_);
return v___x_235_;
}
case 1:
{
lean_object* v_it_236_; lean_object* v___x_237_; 
lean_dec(v_toBind_229_);
lean_dec(v___y_227_);
lean_dec(v_toPure_225_);
v_it_236_ = lean_ctor_get(v_s_230_, 0);
lean_inc(v_it_236_);
lean_dec_ref_known(v_s_230_, 1);
v___x_237_ = lean_apply_4(v_recur_226_, v_it_236_, v_acc_228_, lean_box(0), lean_box(0));
return v___x_237_;
}
default: 
{
lean_object* v___x_238_; 
lean_dec(v_toBind_229_);
lean_dec(v___y_227_);
lean_dec(v_recur_226_);
v___x_238_ = lean_apply_2(v_toPure_225_, lean_box(0), v_acc_228_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(lean_object* v_inst_239_, lean_object* v_toPure_240_, lean_object* v___y_241_, lean_object* v_toBind_242_, lean_object* v_inst_243_, lean_object* v_lift_244_, lean_object* v_inst_245_, lean_object* v_it_246_, lean_object* v_acc_247_, lean_object* v_hP_248_, lean_object* v_recur_249_){
_start:
{
lean_object* v_toApplicative_250_; lean_object* v_toBind_251_; lean_object* v_toPure_252_; lean_object* v_left_253_; lean_object* v_memoizedLeft_254_; lean_object* v_right_255_; lean_object* v___f_256_; 
v_toApplicative_250_ = lean_ctor_get(v_inst_239_, 0);
lean_inc_ref(v_toApplicative_250_);
v_toBind_251_ = lean_ctor_get(v_inst_239_, 1);
lean_inc(v_toBind_251_);
lean_dec_ref(v_inst_239_);
v_toPure_252_ = lean_ctor_get(v_toApplicative_250_, 1);
lean_inc(v_toPure_252_);
lean_dec_ref(v_toApplicative_250_);
v_left_253_ = lean_ctor_get(v_it_246_, 0);
lean_inc(v_left_253_);
v_memoizedLeft_254_ = lean_ctor_get(v_it_246_, 1);
lean_inc(v_memoizedLeft_254_);
v_right_255_ = lean_ctor_get(v_it_246_, 2);
lean_inc(v_right_255_);
lean_dec_ref(v_it_246_);
v___f_256_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_256_, 0, v_toPure_240_);
lean_closure_set(v___f_256_, 1, v_recur_249_);
lean_closure_set(v___f_256_, 2, v___y_241_);
lean_closure_set(v___f_256_, 3, v_acc_247_);
lean_closure_set(v___f_256_, 4, v_toBind_242_);
if (lean_obj_tag(v_memoizedLeft_254_) == 0)
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_inst_245_);
v___f_257_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0), 4, 3);
lean_closure_set(v___f_257_, 0, v_right_255_);
lean_closure_set(v___f_257_, 1, v_toPure_252_);
lean_closure_set(v___f_257_, 2, v_memoizedLeft_254_);
v___x_258_ = lean_apply_1(v_inst_243_, v_left_253_);
v___x_259_ = lean_apply_4(v_toBind_251_, lean_box(0), lean_box(0), v___x_258_, v___f_257_);
v___x_260_ = lean_apply_4(v_lift_244_, lean_box(0), lean_box(0), v___f_256_, v___x_259_);
return v___x_260_;
}
else
{
lean_object* v_val_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_inst_243_);
v_val_261_ = lean_ctor_get(v_memoizedLeft_254_, 0);
lean_inc(v_val_261_);
v___f_262_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1), 5, 4);
lean_closure_set(v___f_262_, 0, v_left_253_);
lean_closure_set(v___f_262_, 1, v_val_261_);
lean_closure_set(v___f_262_, 2, v_toPure_252_);
lean_closure_set(v___f_262_, 3, v_memoizedLeft_254_);
v___x_263_ = lean_apply_1(v_inst_245_, v_right_255_);
v___x_264_ = lean_apply_4(v_toBind_251_, lean_box(0), lean_box(0), v___x_263_, v___f_262_);
v___x_265_ = lean_apply_4(v_lift_244_, lean_box(0), lean_box(0), v___f_256_, v___x_264_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_lift_270_, lean_object* v_00_u03b3_271_, lean_object* v_Pl_272_, lean_object* v_it_273_, lean_object* v_init_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_toApplicative_276_; lean_object* v_toBind_277_; lean_object* v_toPure_278_; lean_object* v___f_279_; lean_object* v___x_280_; 
v_toApplicative_276_ = lean_ctor_get(v_inst_266_, 0);
lean_inc_ref(v_toApplicative_276_);
v_toBind_277_ = lean_ctor_get(v_inst_266_, 1);
lean_inc(v_toBind_277_);
lean_dec_ref(v_inst_266_);
v_toPure_278_ = lean_ctor_get(v_toApplicative_276_, 1);
lean_inc(v_toPure_278_);
lean_dec_ref(v_toApplicative_276_);
v___f_279_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_279_, 0, v_inst_267_);
lean_closure_set(v___f_279_, 1, v_toPure_278_);
lean_closure_set(v___f_279_, 2, v___y_275_);
lean_closure_set(v___f_279_, 3, v_toBind_277_);
lean_closure_set(v___f_279_, 4, v_inst_268_);
lean_closure_set(v___f_279_, 5, v_lift_270_);
lean_closure_set(v___f_279_, 6, v_inst_269_);
v___x_280_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_279_, v_it_273_, v_init_274_, lean_box(0));
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_285_, 0, v_inst_284_);
lean_closure_set(v___f_285_, 1, v_inst_283_);
lean_closure_set(v___f_285_, 2, v_inst_281_);
lean_closure_set(v___f_285_, 3, v_inst_282_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop(lean_object* v_m_286_, lean_object* v_00_u03b1_u2081_287_, lean_object* v_00_u03b2_u2081_288_, lean_object* v_inst_289_, lean_object* v_00_u03b1_u2082_290_, lean_object* v_00_u03b2_u2082_291_, lean_object* v_inst_292_, lean_object* v_n_293_, lean_object* v_inst_294_, lean_object* v_inst_295_){
_start:
{
lean_object* v___f_296_; 
v___f_296_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_296_, 0, v_inst_295_);
lean_closure_set(v___f_296_, 1, v_inst_294_);
lean_closure_set(v___f_296_, 2, v_inst_289_);
lean_closure_set(v___f_296_, 3, v_inst_292_);
return v___f_296_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
