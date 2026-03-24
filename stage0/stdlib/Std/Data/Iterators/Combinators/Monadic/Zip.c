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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_____do__lift_27_);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object* v_m_109_, lean_object* v_00_u03b1_u2081_110_, lean_object* v_00_u03b2_u2081_111_, lean_object* v_inst_112_, lean_object* v_00_u03b1_u2082_113_, lean_object* v_00_u03b2_u2082_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_inst_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_box(0);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object* v_m_120_, lean_object* v_00_u03b1_u2081_121_, lean_object* v_00_u03b2_u2081_122_, lean_object* v_inst_123_, lean_object* v_00_u03b1_u2082_124_, lean_object* v_00_u03b2_u2082_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(v_m_120_, v_00_u03b1_u2081_121_, v_00_u03b2_u2081_122_, v_inst_123_, v_00_u03b1_u2082_124_, v_00_u03b2_u2082_125_, v_inst_126_, v_inst_127_, v_inst_128_, v_inst_129_);
lean_dec_ref(v_inst_127_);
lean_dec(v_inst_126_);
lean_dec(v_inst_123_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(lean_object* v_x_131_, lean_object* v_x_132_, lean_object* v_h__1_133_, lean_object* v_h__2_134_, lean_object* v_h__3_135_){
_start:
{
if (lean_obj_tag(v_x_131_) == 0)
{
lean_object* v___x_136_; 
lean_dec(v_h__3_135_);
lean_dec(v_h__2_134_);
v___x_136_ = lean_apply_1(v_h__1_133_, v_x_132_);
return v___x_136_;
}
else
{
lean_dec(v_h__1_133_);
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_val_137_; lean_object* v___x_138_; 
lean_dec(v_h__3_135_);
v_val_137_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_val_137_);
lean_dec_ref(v_x_131_);
v___x_138_ = lean_apply_1(v_h__2_134_, v_val_137_);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v_val_140_; lean_object* v___x_141_; 
lean_dec(v_h__2_134_);
v_val_139_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_val_139_);
lean_dec_ref(v_x_131_);
v_val_140_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_val_140_);
lean_dec_ref(v_x_132_);
v___x_141_ = lean_apply_2(v_h__3_135_, v_val_139_, v_val_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(lean_object* v_00_u03b2_142_, lean_object* v_00_u03b1_143_, lean_object* v_motive_144_, lean_object* v_x_145_, lean_object* v_x_146_, lean_object* v_h__1_147_, lean_object* v_h__2_148_, lean_object* v_h__3_149_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_150_; 
lean_dec(v_h__3_149_);
lean_dec(v_h__2_148_);
v___x_150_ = lean_apply_1(v_h__1_147_, v_x_146_);
return v___x_150_;
}
else
{
lean_dec(v_h__1_147_);
if (lean_obj_tag(v_x_146_) == 0)
{
lean_object* v_val_151_; lean_object* v___x_152_; 
lean_dec(v_h__3_149_);
v_val_151_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v_x_145_);
v___x_152_ = lean_apply_1(v_h__2_148_, v_val_151_);
return v___x_152_;
}
else
{
lean_object* v_val_153_; lean_object* v_val_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_148_);
v_val_153_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_val_153_);
lean_dec_ref(v_x_145_);
v_val_154_ = lean_ctor_get(v_x_146_, 0);
lean_inc(v_val_154_);
lean_dec_ref(v_x_146_);
v___x_155_ = lean_apply_2(v_h__3_149_, v_val_153_, v_val_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(lean_object* v_m_156_, lean_object* v_00_u03b1_u2081_157_, lean_object* v_00_u03b2_u2081_158_, lean_object* v_inst_159_, lean_object* v_00_u03b1_u2082_160_, lean_object* v_00_u03b2_u2082_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_inst_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(lean_object* v_m_167_, lean_object* v_00_u03b1_u2081_168_, lean_object* v_00_u03b2_u2081_169_, lean_object* v_inst_170_, lean_object* v_00_u03b1_u2082_171_, lean_object* v_00_u03b2_u2082_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(v_m_167_, v_00_u03b1_u2081_168_, v_00_u03b2_u2081_169_, v_inst_170_, v_00_u03b1_u2082_171_, v_00_u03b2_u2082_172_, v_inst_173_, v_inst_174_, v_inst_175_, v_inst_176_);
lean_dec_ref(v_inst_174_);
lean_dec(v_inst_173_);
lean_dec(v_inst_170_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation(lean_object* v_m_178_, lean_object* v_00_u03b1_u2081_179_, lean_object* v_00_u03b2_u2081_180_, lean_object* v_inst_181_, lean_object* v_00_u03b1_u2082_182_, lean_object* v_00_u03b2_u2082_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = lean_box(0);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(lean_object* v_m_189_, lean_object* v_00_u03b1_u2081_190_, lean_object* v_00_u03b2_u2081_191_, lean_object* v_inst_192_, lean_object* v_00_u03b1_u2082_193_, lean_object* v_00_u03b2_u2082_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Iterators_Types_Zip_instProductivenessRelation(v_m_189_, v_00_u03b1_u2081_190_, v_00_u03b2_u2081_191_, v_inst_192_, v_00_u03b1_u2082_193_, v_00_u03b2_u2082_194_, v_inst_195_, v_inst_196_, v_inst_197_, v_inst_198_);
lean_dec_ref(v_inst_196_);
lean_dec(v_inst_195_);
lean_dec(v_inst_192_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_200_, lean_object* v_recur_201_, lean_object* v_it_202_, lean_object* v_____do__lift_203_){
_start:
{
if (lean_obj_tag(v_____do__lift_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_205_; 
lean_dec_ref(v_it_202_);
lean_dec(v_recur_201_);
v_a_204_ = lean_ctor_get(v_____do__lift_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref(v_____do__lift_203_);
v___x_205_ = lean_apply_2(v_toPure_200_, lean_box(0), v_a_204_);
return v___x_205_;
}
else
{
lean_object* v_a_206_; lean_object* v___x_207_; 
lean_dec(v_toPure_200_);
v_a_206_ = lean_ctor_get(v_____do__lift_203_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v_____do__lift_203_);
v___x_207_ = lean_apply_4(v_recur_201_, v_it_202_, v_a_206_, lean_box(0), lean_box(0));
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_208_, lean_object* v_recur_209_, lean_object* v___y_210_, lean_object* v_acc_211_, lean_object* v_toBind_212_, lean_object* v_s_213_){
_start:
{
switch(lean_obj_tag(v_s_213_))
{
case 0:
{
lean_object* v_it_214_; lean_object* v_out_215_; lean_object* v___f_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v_it_214_ = lean_ctor_get(v_s_213_, 0);
lean_inc(v_it_214_);
v_out_215_ = lean_ctor_get(v_s_213_, 1);
lean_inc(v_out_215_);
lean_dec_ref(v_s_213_);
v___f_216_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_216_, 0, v_toPure_208_);
lean_closure_set(v___f_216_, 1, v_recur_209_);
lean_closure_set(v___f_216_, 2, v_it_214_);
v___x_217_ = lean_apply_3(v___y_210_, v_out_215_, lean_box(0), v_acc_211_);
v___x_218_ = lean_apply_4(v_toBind_212_, lean_box(0), lean_box(0), v___x_217_, v___f_216_);
return v___x_218_;
}
case 1:
{
lean_object* v_it_219_; lean_object* v___x_220_; 
lean_dec(v_toBind_212_);
lean_dec(v___y_210_);
lean_dec(v_toPure_208_);
v_it_219_ = lean_ctor_get(v_s_213_, 0);
lean_inc(v_it_219_);
lean_dec_ref(v_s_213_);
v___x_220_ = lean_apply_4(v_recur_209_, v_it_219_, v_acc_211_, lean_box(0), lean_box(0));
return v___x_220_;
}
default: 
{
lean_object* v___x_221_; 
lean_dec(v_toBind_212_);
lean_dec(v___y_210_);
lean_dec(v_recur_209_);
v___x_221_ = lean_apply_2(v_toPure_208_, lean_box(0), v_acc_211_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(lean_object* v_inst_222_, lean_object* v_toPure_223_, lean_object* v___y_224_, lean_object* v_toBind_225_, lean_object* v_inst_226_, lean_object* v_lift_227_, lean_object* v_inst_228_, lean_object* v_it_229_, lean_object* v_acc_230_, lean_object* v_hP_231_, lean_object* v_recur_232_){
_start:
{
lean_object* v_toApplicative_233_; lean_object* v_toBind_234_; lean_object* v_toPure_235_; lean_object* v_left_236_; lean_object* v_memoizedLeft_237_; lean_object* v_right_238_; lean_object* v___f_239_; 
v_toApplicative_233_ = lean_ctor_get(v_inst_222_, 0);
lean_inc_ref(v_toApplicative_233_);
v_toBind_234_ = lean_ctor_get(v_inst_222_, 1);
lean_inc(v_toBind_234_);
lean_dec_ref(v_inst_222_);
v_toPure_235_ = lean_ctor_get(v_toApplicative_233_, 1);
lean_inc(v_toPure_235_);
lean_dec_ref(v_toApplicative_233_);
v_left_236_ = lean_ctor_get(v_it_229_, 0);
lean_inc(v_left_236_);
v_memoizedLeft_237_ = lean_ctor_get(v_it_229_, 1);
lean_inc(v_memoizedLeft_237_);
v_right_238_ = lean_ctor_get(v_it_229_, 2);
lean_inc(v_right_238_);
lean_dec_ref(v_it_229_);
v___f_239_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_239_, 0, v_toPure_223_);
lean_closure_set(v___f_239_, 1, v_recur_232_);
lean_closure_set(v___f_239_, 2, v___y_224_);
lean_closure_set(v___f_239_, 3, v_acc_230_);
lean_closure_set(v___f_239_, 4, v_toBind_225_);
if (lean_obj_tag(v_memoizedLeft_237_) == 0)
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_inst_228_);
v___f_240_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0), 4, 3);
lean_closure_set(v___f_240_, 0, v_right_238_);
lean_closure_set(v___f_240_, 1, v_toPure_235_);
lean_closure_set(v___f_240_, 2, v_memoizedLeft_237_);
v___x_241_ = lean_apply_1(v_inst_226_, v_left_236_);
v___x_242_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_241_, v___f_240_);
v___x_243_ = lean_apply_4(v_lift_227_, lean_box(0), lean_box(0), v___f_239_, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_inst_226_);
v_val_244_ = lean_ctor_get(v_memoizedLeft_237_, 0);
lean_inc(v_val_244_);
v___f_245_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1), 5, 4);
lean_closure_set(v___f_245_, 0, v_left_236_);
lean_closure_set(v___f_245_, 1, v_val_244_);
lean_closure_set(v___f_245_, 2, v_toPure_235_);
lean_closure_set(v___f_245_, 3, v_memoizedLeft_237_);
v___x_246_ = lean_apply_1(v_inst_228_, v_right_238_);
v___x_247_ = lean_apply_4(v_toBind_234_, lean_box(0), lean_box(0), v___x_246_, v___f_245_);
v___x_248_ = lean_apply_4(v_lift_227_, lean_box(0), lean_box(0), v___f_239_, v___x_247_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_lift_253_, lean_object* v_00_u03b3_254_, lean_object* v_Pl_255_, lean_object* v_it_256_, lean_object* v_init_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v_toBind_260_; lean_object* v_toPure_261_; lean_object* v___f_262_; lean_object* v___x_263_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_249_, 0);
lean_inc_ref(v_toApplicative_259_);
v_toBind_260_ = lean_ctor_get(v_inst_249_, 1);
lean_inc(v_toBind_260_);
lean_dec_ref(v_inst_249_);
v_toPure_261_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_261_);
lean_dec_ref(v_toApplicative_259_);
v___f_262_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_262_, 0, v_inst_250_);
lean_closure_set(v___f_262_, 1, v_toPure_261_);
lean_closure_set(v___f_262_, 2, v___y_258_);
lean_closure_set(v___f_262_, 3, v_toBind_260_);
lean_closure_set(v___f_262_, 4, v_inst_251_);
lean_closure_set(v___f_262_, 5, v_lift_253_);
lean_closure_set(v___f_262_, 6, v_inst_252_);
v___x_263_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_262_, v_it_256_, v_init_257_, lean_box(0));
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___f_268_; 
v___f_268_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_268_, 0, v_inst_267_);
lean_closure_set(v___f_268_, 1, v_inst_266_);
lean_closure_set(v___f_268_, 2, v_inst_264_);
lean_closure_set(v___f_268_, 3, v_inst_265_);
return v___f_268_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop(lean_object* v_m_269_, lean_object* v_00_u03b1_u2081_270_, lean_object* v_00_u03b2_u2081_271_, lean_object* v_inst_272_, lean_object* v_00_u03b1_u2082_273_, lean_object* v_00_u03b2_u2082_274_, lean_object* v_inst_275_, lean_object* v_n_276_, lean_object* v_inst_277_, lean_object* v_inst_278_){
_start:
{
lean_object* v___f_279_; 
v___f_279_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_279_, 0, v_inst_278_);
lean_closure_set(v___f_279_, 1, v_inst_277_);
lean_closure_set(v___f_279_, 2, v_inst_272_);
lean_closure_set(v___f_279_, 3, v_inst_275_);
return v___f_279_;
}
}
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
