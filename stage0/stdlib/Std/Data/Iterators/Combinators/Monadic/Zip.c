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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg(){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg___boxed(lean_object* v___dummy_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___redArg();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(lean_object* v_m_113_, lean_object* v_00_u03b1_u2081_114_, lean_object* v_00_u03b2_u2081_115_, lean_object* v_inst_116_, lean_object* v_00_u03b1_u2082_117_, lean_object* v_00_u03b2_u2082_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081___boxed(lean_object* v_m_124_, lean_object* v_00_u03b1_u2081_125_, lean_object* v_00_u03b2_u2081_126_, lean_object* v_inst_127_, lean_object* v_00_u03b1_u2082_128_, lean_object* v_00_u03b2_u2082_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_inst_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2081(v_m_124_, v_00_u03b1_u2081_125_, v_00_u03b2_u2081_126_, v_inst_127_, v_00_u03b1_u2082_128_, v_00_u03b2_u2082_129_, v_inst_130_, v_inst_131_, v_inst_132_, v_inst_133_);
lean_dec_ref(v_inst_131_);
lean_dec(v_inst_130_);
lean_dec(v_inst_127_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter___redArg(lean_object* v_x_135_, lean_object* v_x_136_, lean_object* v_h__1_137_, lean_object* v_h__2_138_, lean_object* v_h__3_139_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v___x_140_; 
lean_dec(v_h__3_139_);
lean_dec(v_h__2_138_);
v___x_140_ = lean_apply_1(v_h__1_137_, v_x_136_);
return v___x_140_;
}
else
{
lean_dec(v_h__1_137_);
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_val_141_; lean_object* v___x_142_; 
lean_dec(v_h__3_139_);
v_val_141_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_val_141_);
lean_dec_ref_known(v_x_135_, 1);
v___x_142_ = lean_apply_1(v_h__2_138_, v_val_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v_val_144_; lean_object* v___x_145_; 
lean_dec(v_h__2_138_);
v_val_143_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v_x_135_, 1);
v_val_144_ = lean_ctor_get(v_x_136_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v_x_136_, 1);
v___x_145_ = lean_apply_2(v_h__3_139_, v_val_143_, v_val_144_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Combinators_Monadic_Zip_0__Option_SomeLtNone_lt_match__1_splitter(lean_object* v_00_u03b2_146_, lean_object* v_00_u03b1_147_, lean_object* v_motive_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_h__1_151_, lean_object* v_h__2_152_, lean_object* v_h__3_153_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v___x_154_; 
lean_dec(v_h__3_153_);
lean_dec(v_h__2_152_);
v___x_154_ = lean_apply_1(v_h__1_151_, v_x_150_);
return v___x_154_;
}
else
{
lean_dec(v_h__1_151_);
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v_val_155_; lean_object* v___x_156_; 
lean_dec(v_h__3_153_);
v_val_155_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v_x_149_, 1);
v___x_156_ = lean_apply_1(v_h__2_152_, v_val_155_);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v_val_158_; lean_object* v___x_159_; 
lean_dec(v_h__2_152_);
v_val_157_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v_x_149_, 1);
v_val_158_ = lean_ctor_get(v_x_150_, 0);
lean_inc(v_val_158_);
lean_dec_ref_known(v_x_150_, 1);
v___x_159_ = lean_apply_2(v_h__3_153_, v_val_157_, v_val_158_);
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg(){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg___boxed(lean_object* v___dummy_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___redArg();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(lean_object* v_m_164_, lean_object* v_00_u03b1_u2081_165_, lean_object* v_00_u03b2_u2081_166_, lean_object* v_inst_167_, lean_object* v_00_u03b1_u2082_168_, lean_object* v_00_u03b2_u2082_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082___boxed(lean_object* v_m_175_, lean_object* v_00_u03b1_u2081_176_, lean_object* v_00_u03b2_u2081_177_, lean_object* v_inst_178_, lean_object* v_00_u03b1_u2082_179_, lean_object* v_00_u03b2_u2082_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_inst_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Iterators_Types_Zip_instFinitenessRelation_u2082(v_m_175_, v_00_u03b1_u2081_176_, v_00_u03b2_u2081_177_, v_inst_178_, v_00_u03b1_u2082_179_, v_00_u03b2_u2082_180_, v_inst_181_, v_inst_182_, v_inst_183_, v_inst_184_);
lean_dec_ref(v_inst_182_);
lean_dec(v_inst_181_);
lean_dec(v_inst_178_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_box(0);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Iterators_Types_Zip_instProductivenessRelation___redArg();
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation(lean_object* v_m_190_, lean_object* v_00_u03b1_u2081_191_, lean_object* v_00_u03b2_u2081_192_, lean_object* v_inst_193_, lean_object* v_00_u03b1_u2082_194_, lean_object* v_00_u03b2_u2082_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instProductivenessRelation___boxed(lean_object* v_m_201_, lean_object* v_00_u03b1_u2081_202_, lean_object* v_00_u03b2_u2081_203_, lean_object* v_inst_204_, lean_object* v_00_u03b1_u2082_205_, lean_object* v_00_u03b2_u2082_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Iterators_Types_Zip_instProductivenessRelation(v_m_201_, v_00_u03b1_u2081_202_, v_00_u03b2_u2081_203_, v_inst_204_, v_00_u03b1_u2082_205_, v_00_u03b2_u2082_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_inst_210_);
lean_dec_ref(v_inst_208_);
lean_dec(v_inst_207_);
lean_dec(v_inst_204_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_212_, lean_object* v_recur_213_, lean_object* v_it_214_, lean_object* v_____do__lift_215_){
_start:
{
if (lean_obj_tag(v_____do__lift_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_217_; 
lean_dec_ref(v_it_214_);
lean_dec(v_recur_213_);
v_a_216_ = lean_ctor_get(v_____do__lift_215_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v_____do__lift_215_, 1);
v___x_217_ = lean_apply_2(v_toPure_212_, lean_box(0), v_a_216_);
return v___x_217_;
}
else
{
lean_object* v_a_218_; lean_object* v___x_219_; 
lean_dec(v_toPure_212_);
v_a_218_ = lean_ctor_get(v_____do__lift_215_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v_____do__lift_215_, 1);
v___x_219_ = lean_apply_4(v_recur_213_, v_it_214_, v_a_218_, lean_box(0), lean_box(0));
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_220_, lean_object* v_recur_221_, lean_object* v___y_222_, lean_object* v_acc_223_, lean_object* v_toBind_224_, lean_object* v_s_225_){
_start:
{
switch(lean_obj_tag(v_s_225_))
{
case 0:
{
lean_object* v_it_226_; lean_object* v_out_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_it_226_ = lean_ctor_get(v_s_225_, 0);
lean_inc(v_it_226_);
v_out_227_ = lean_ctor_get(v_s_225_, 1);
lean_inc(v_out_227_);
lean_dec_ref_known(v_s_225_, 2);
v___f_228_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_228_, 0, v_toPure_220_);
lean_closure_set(v___f_228_, 1, v_recur_221_);
lean_closure_set(v___f_228_, 2, v_it_226_);
v___x_229_ = lean_apply_3(v___y_222_, v_out_227_, lean_box(0), v_acc_223_);
v___x_230_ = lean_apply_4(v_toBind_224_, lean_box(0), lean_box(0), v___x_229_, v___f_228_);
return v___x_230_;
}
case 1:
{
lean_object* v_it_231_; lean_object* v___x_232_; 
lean_dec(v_toBind_224_);
lean_dec(v___y_222_);
lean_dec(v_toPure_220_);
v_it_231_ = lean_ctor_get(v_s_225_, 0);
lean_inc(v_it_231_);
lean_dec_ref_known(v_s_225_, 1);
v___x_232_ = lean_apply_4(v_recur_221_, v_it_231_, v_acc_223_, lean_box(0), lean_box(0));
return v___x_232_;
}
default: 
{
lean_object* v___x_233_; 
lean_dec(v_toBind_224_);
lean_dec(v___y_222_);
lean_dec(v_recur_221_);
v___x_233_ = lean_apply_2(v_toPure_220_, lean_box(0), v_acc_223_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4(lean_object* v_inst_234_, lean_object* v_toPure_235_, lean_object* v___y_236_, lean_object* v_toBind_237_, lean_object* v_inst_238_, lean_object* v_lift_239_, lean_object* v_inst_240_, lean_object* v_it_241_, lean_object* v_acc_242_, lean_object* v_hP_243_, lean_object* v_recur_244_){
_start:
{
lean_object* v_toApplicative_245_; lean_object* v_toBind_246_; lean_object* v_toPure_247_; lean_object* v_left_248_; lean_object* v_memoizedLeft_249_; lean_object* v_right_250_; lean_object* v___f_251_; 
v_toApplicative_245_ = lean_ctor_get(v_inst_234_, 0);
lean_inc_ref(v_toApplicative_245_);
v_toBind_246_ = lean_ctor_get(v_inst_234_, 1);
lean_inc(v_toBind_246_);
lean_dec_ref(v_inst_234_);
v_toPure_247_ = lean_ctor_get(v_toApplicative_245_, 1);
lean_inc(v_toPure_247_);
lean_dec_ref(v_toApplicative_245_);
v_left_248_ = lean_ctor_get(v_it_241_, 0);
lean_inc(v_left_248_);
v_memoizedLeft_249_ = lean_ctor_get(v_it_241_, 1);
lean_inc(v_memoizedLeft_249_);
v_right_250_ = lean_ctor_get(v_it_241_, 2);
lean_inc(v_right_250_);
lean_dec_ref(v_it_241_);
v___f_251_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_251_, 0, v_toPure_235_);
lean_closure_set(v___f_251_, 1, v_recur_244_);
lean_closure_set(v___f_251_, 2, v___y_236_);
lean_closure_set(v___f_251_, 3, v_acc_242_);
lean_closure_set(v___f_251_, 4, v_toBind_237_);
if (lean_obj_tag(v_memoizedLeft_249_) == 0)
{
lean_object* v___f_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_inst_240_);
v___f_252_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__0), 4, 3);
lean_closure_set(v___f_252_, 0, v_right_250_);
lean_closure_set(v___f_252_, 1, v_toPure_247_);
lean_closure_set(v___f_252_, 2, v_memoizedLeft_249_);
v___x_253_ = lean_apply_1(v_inst_238_, v_left_248_);
v___x_254_ = lean_apply_4(v_toBind_246_, lean_box(0), lean_box(0), v___x_253_, v___f_252_);
v___x_255_ = lean_apply_4(v_lift_239_, lean_box(0), lean_box(0), v___f_251_, v___x_254_);
return v___x_255_;
}
else
{
lean_object* v_val_256_; lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec(v_inst_238_);
v_val_256_ = lean_ctor_get(v_memoizedLeft_249_, 0);
lean_inc(v_val_256_);
v___f_257_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIterator___redArg___lam__1), 5, 4);
lean_closure_set(v___f_257_, 0, v_left_248_);
lean_closure_set(v___f_257_, 1, v_val_256_);
lean_closure_set(v___f_257_, 2, v_toPure_247_);
lean_closure_set(v___f_257_, 3, v_memoizedLeft_249_);
v___x_258_ = lean_apply_1(v_inst_240_, v_right_250_);
v___x_259_ = lean_apply_4(v_toBind_246_, lean_box(0), lean_box(0), v___x_258_, v___f_257_);
v___x_260_ = lean_apply_4(v_lift_239_, lean_box(0), lean_box(0), v___f_251_, v___x_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2(lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_, lean_object* v_lift_265_, lean_object* v_00_u03b3_266_, lean_object* v_Pl_267_, lean_object* v_it_268_, lean_object* v_init_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_toApplicative_271_; lean_object* v_toBind_272_; lean_object* v_toPure_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v_toApplicative_271_ = lean_ctor_get(v_inst_261_, 0);
lean_inc_ref(v_toApplicative_271_);
v_toBind_272_ = lean_ctor_get(v_inst_261_, 1);
lean_inc(v_toBind_272_);
lean_dec_ref(v_inst_261_);
v_toPure_273_ = lean_ctor_get(v_toApplicative_271_, 1);
lean_inc(v_toPure_273_);
lean_dec_ref(v_toApplicative_271_);
v___f_274_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__4), 11, 7);
lean_closure_set(v___f_274_, 0, v_inst_262_);
lean_closure_set(v___f_274_, 1, v_toPure_273_);
lean_closure_set(v___f_274_, 2, v___y_270_);
lean_closure_set(v___f_274_, 3, v_toBind_272_);
lean_closure_set(v___f_274_, 4, v_inst_263_);
lean_closure_set(v___f_274_, 5, v_lift_265_);
lean_closure_set(v___f_274_, 6, v_inst_264_);
v___x_275_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_274_, v_it_268_, v_init_269_, lean_box(0));
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_280_, 0, v_inst_279_);
lean_closure_set(v___f_280_, 1, v_inst_278_);
lean_closure_set(v___f_280_, 2, v_inst_276_);
lean_closure_set(v___f_280_, 3, v_inst_277_);
return v___f_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Zip_instIteratorLoop(lean_object* v_m_281_, lean_object* v_00_u03b1_u2081_282_, lean_object* v_00_u03b2_u2081_283_, lean_object* v_inst_284_, lean_object* v_00_u03b1_u2082_285_, lean_object* v_00_u03b2_u2082_286_, lean_object* v_inst_287_, lean_object* v_n_288_, lean_object* v_inst_289_, lean_object* v_inst_290_){
_start:
{
lean_object* v___f_291_; 
v___f_291_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Zip_instIteratorLoop___redArg___lam__2), 10, 4);
lean_closure_set(v___f_291_, 0, v_inst_290_);
lean_closure_set(v___f_291_, 1, v_inst_289_);
lean_closure_set(v___f_291_, 2, v_inst_284_);
lean_closure_set(v___f_291_, 3, v_inst_287_);
return v___f_291_;
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
