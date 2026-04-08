// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Attach
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_attachWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep___redArg(lean_object* v_step_1_){
_start:
{
switch(lean_obj_tag(v_step_1_))
{
case 0:
{
lean_object* v_it_2_; lean_object* v_out_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_10_; 
v_it_2_ = lean_ctor_get(v_step_1_, 0);
v_out_3_ = lean_ctor_get(v_step_1_, 1);
v_isSharedCheck_10_ = !lean_is_exclusive(v_step_1_);
if (v_isSharedCheck_10_ == 0)
{
v___x_5_ = v_step_1_;
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_out_3_);
lean_inc(v_it_2_);
lean_dec(v_step_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_10_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_9_; 
v_reuseFailAlloc_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_9_, 0, v_it_2_);
lean_ctor_set(v_reuseFailAlloc_9_, 1, v_out_3_);
v___x_8_ = v_reuseFailAlloc_9_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
return v___x_8_;
}
}
}
case 1:
{
lean_object* v_it_11_; lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_18_; 
v_it_11_ = lean_ctor_get(v_step_1_, 0);
v_isSharedCheck_18_ = !lean_is_exclusive(v_step_1_);
if (v_isSharedCheck_18_ == 0)
{
v___x_13_ = v_step_1_;
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
else
{
lean_inc(v_it_11_);
lean_dec(v_step_1_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_18_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_16_; 
if (v_isShared_14_ == 0)
{
v___x_16_ = v___x_13_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v_it_11_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
default: 
{
lean_object* v___x_19_; 
v___x_19_ = lean_box(2);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep(lean_object* v_00_u03b1_20_, lean_object* v_m_21_, lean_object* v_00_u03b2_22_, lean_object* v_inst_23_, lean_object* v_P_24_, lean_object* v_it_25_, lean_object* v_step_26_){
_start:
{
switch(lean_obj_tag(v_step_26_))
{
case 0:
{
lean_object* v_it_27_; lean_object* v_out_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_it_27_ = lean_ctor_get(v_step_26_, 0);
v_out_28_ = lean_ctor_get(v_step_26_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v_step_26_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v_step_26_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_out_28_);
lean_inc(v_it_27_);
lean_dec(v_step_26_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_it_27_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_out_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
case 1:
{
lean_object* v_it_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_it_36_ = lean_ctor_get(v_step_26_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_step_26_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v_step_26_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_it_36_);
lean_dec(v_step_26_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_it_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
default: 
{
lean_object* v___x_44_; 
v___x_44_ = lean_box(2);
return v___x_44_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_Monadic_modifyStep___boxed(lean_object* v_00_u03b1_45_, lean_object* v_m_46_, lean_object* v_00_u03b2_47_, lean_object* v_inst_48_, lean_object* v_P_49_, lean_object* v_it_50_, lean_object* v_step_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Iterators_Types_Attach_Monadic_modifyStep(v_00_u03b1_45_, v_m_46_, v_00_u03b2_47_, v_inst_48_, v_P_49_, v_it_50_, v_step_51_);
lean_dec(v_it_50_);
lean_dec(v_inst_48_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg___lam__0(lean_object* v_step_53_){
_start:
{
switch(lean_obj_tag(v_step_53_))
{
case 0:
{
lean_object* v_it_54_; lean_object* v_out_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
v_it_54_ = lean_ctor_get(v_step_53_, 0);
v_out_55_ = lean_ctor_get(v_step_53_, 1);
v_isSharedCheck_62_ = !lean_is_exclusive(v_step_53_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v_step_53_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_out_55_);
lean_inc(v_it_54_);
lean_dec(v_step_53_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_it_54_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_out_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
case 1:
{
lean_object* v_it_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
v_it_63_ = lean_ctor_get(v_step_53_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_step_53_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v_step_53_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_it_63_);
lean_dec(v_step_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_it_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
default: 
{
lean_object* v___x_71_; 
v___x_71_ = lean_box(2);
return v___x_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1(lean_object* v_toFunctor_72_, lean_object* v_inst_73_, lean_object* v___f_74_, lean_object* v_it_75_){
_start:
{
lean_object* v_map_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v_map_76_ = lean_ctor_get(v_toFunctor_72_, 0);
lean_inc(v_map_76_);
lean_dec_ref(v_toFunctor_72_);
v___x_77_ = lean_apply_1(v_inst_73_, v_it_75_);
v___x_78_ = lean_apply_4(v_map_76_, lean_box(0), lean_box(0), v___f_74_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator___redArg(lean_object* v_inst_80_, lean_object* v_inst_81_){
_start:
{
lean_object* v_toApplicative_82_; lean_object* v_toFunctor_83_; lean_object* v___f_84_; lean_object* v___f_85_; 
v_toApplicative_82_ = lean_ctor_get(v_inst_80_, 0);
lean_inc_ref(v_toApplicative_82_);
lean_dec_ref(v_inst_80_);
v_toFunctor_83_ = lean_ctor_get(v_toApplicative_82_, 0);
lean_inc_ref(v_toFunctor_83_);
lean_dec_ref(v_toApplicative_82_);
v___f_84_ = ((lean_object*)(l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0));
v___f_85_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_85_, 0, v_toFunctor_83_);
lean_closure_set(v___f_85_, 1, v_inst_81_);
lean_closure_set(v___f_85_, 2, v___f_84_);
return v___f_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIterator(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_m_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_P_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Std_Iterators_Types_Attach_instIterator___redArg(v_inst_89_, v_inst_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___redArg(lean_object* v_step_93_, lean_object* v_h__1_94_, lean_object* v_h__2_95_, lean_object* v_h__3_96_){
_start:
{
switch(lean_obj_tag(v_step_93_))
{
case 0:
{
lean_object* v_it_97_; lean_object* v_out_98_; lean_object* v___x_99_; 
lean_dec(v_h__3_96_);
lean_dec(v_h__2_95_);
v_it_97_ = lean_ctor_get(v_step_93_, 0);
lean_inc(v_it_97_);
v_out_98_ = lean_ctor_get(v_step_93_, 1);
lean_inc(v_out_98_);
lean_dec_ref(v_step_93_);
v___x_99_ = lean_apply_3(v_h__1_94_, v_it_97_, v_out_98_, lean_box(0));
return v___x_99_;
}
case 1:
{
lean_object* v_it_100_; lean_object* v___x_101_; 
lean_dec(v_h__3_96_);
lean_dec(v_h__1_94_);
v_it_100_ = lean_ctor_get(v_step_93_, 0);
lean_inc(v_it_100_);
lean_dec_ref(v_step_93_);
v___x_101_ = lean_apply_2(v_h__2_95_, v_it_100_, lean_box(0));
return v___x_101_;
}
default: 
{
lean_object* v___x_102_; 
lean_dec(v_h__2_95_);
lean_dec(v_h__1_94_);
v___x_102_ = lean_apply_1(v_h__3_96_, lean_box(0));
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(lean_object* v_00_u03b1_103_, lean_object* v_m_104_, lean_object* v_00_u03b2_105_, lean_object* v_inst_106_, lean_object* v_P_107_, lean_object* v_it_108_, lean_object* v_motive_109_, lean_object* v_step_110_, lean_object* v_h__1_111_, lean_object* v_h__2_112_, lean_object* v_h__3_113_){
_start:
{
switch(lean_obj_tag(v_step_110_))
{
case 0:
{
lean_object* v_it_114_; lean_object* v_out_115_; lean_object* v___x_116_; 
lean_dec(v_h__3_113_);
lean_dec(v_h__2_112_);
v_it_114_ = lean_ctor_get(v_step_110_, 0);
lean_inc(v_it_114_);
v_out_115_ = lean_ctor_get(v_step_110_, 1);
lean_inc(v_out_115_);
lean_dec_ref(v_step_110_);
v___x_116_ = lean_apply_3(v_h__1_111_, v_it_114_, v_out_115_, lean_box(0));
return v___x_116_;
}
case 1:
{
lean_object* v_it_117_; lean_object* v___x_118_; 
lean_dec(v_h__3_113_);
lean_dec(v_h__1_111_);
v_it_117_ = lean_ctor_get(v_step_110_, 0);
lean_inc(v_it_117_);
lean_dec_ref(v_step_110_);
v___x_118_ = lean_apply_2(v_h__2_112_, v_it_117_, lean_box(0));
return v___x_118_;
}
default: 
{
lean_object* v___x_119_; 
lean_dec(v_h__2_112_);
lean_dec(v_h__1_111_);
v___x_119_ = lean_apply_1(v_h__3_113_, lean_box(0));
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter___boxed(lean_object* v_00_u03b1_120_, lean_object* v_m_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_P_124_, lean_object* v_it_125_, lean_object* v_motive_126_, lean_object* v_step_127_, lean_object* v_h__1_128_, lean_object* v_h__2_129_, lean_object* v_h__3_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Init_Data_Iterators_Combinators_Monadic_Attach_0__Std_Iterators_Types_Attach_Monadic_modifyStep_match__1_splitter(v_00_u03b1_120_, v_m_121_, v_00_u03b2_122_, v_inst_123_, v_P_124_, v_it_125_, v_motive_126_, v_step_127_, v_h__1_128_, v_h__2_129_, v_h__3_130_);
lean_dec(v_it_125_);
lean_dec(v_inst_123_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_m_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_, lean_object* v_P_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(0);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_m_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_, lean_object* v_P_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Iterators_Types_Attach_instFinitenessRelation(v_00_u03b1_140_, v_00_u03b2_141_, v_m_142_, v_inst_143_, v_inst_144_, v_inst_145_, v_P_146_);
lean_dec(v_inst_144_);
lean_dec_ref(v_inst_143_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation(lean_object* v_00_u03b1_148_, lean_object* v_00_u03b2_149_, lean_object* v_m_150_, lean_object* v_inst_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_P_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_box(0);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___boxed(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_m_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_P_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Std_Iterators_Types_Attach_instProductivenessRelation(v_00_u03b1_156_, v_00_u03b2_157_, v_m_158_, v_inst_159_, v_inst_160_, v_inst_161_, v_P_162_);
lean_dec(v_inst_160_);
lean_dec_ref(v_inst_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_164_, lean_object* v_recur_165_, lean_object* v_it_166_, lean_object* v_____do__lift_167_){
_start:
{
if (lean_obj_tag(v_____do__lift_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; 
lean_dec(v_it_166_);
lean_dec(v_recur_165_);
v_a_168_ = lean_ctor_get(v_____do__lift_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref(v_____do__lift_167_);
v___x_169_ = lean_apply_2(v_toPure_164_, lean_box(0), v_a_168_);
return v___x_169_;
}
else
{
lean_object* v_a_170_; lean_object* v___x_171_; 
lean_dec(v_toPure_164_);
v_a_170_ = lean_ctor_get(v_____do__lift_167_, 0);
lean_inc(v_a_170_);
lean_dec_ref(v_____do__lift_167_);
v___x_171_ = lean_apply_4(v_recur_165_, v_it_166_, v_a_170_, lean_box(0), lean_box(0));
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_172_, lean_object* v_recur_173_, lean_object* v___y_174_, lean_object* v_acc_175_, lean_object* v_toBind_176_, lean_object* v_s_177_){
_start:
{
switch(lean_obj_tag(v_s_177_))
{
case 0:
{
lean_object* v_it_178_; lean_object* v_out_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_it_178_ = lean_ctor_get(v_s_177_, 0);
lean_inc(v_it_178_);
v_out_179_ = lean_ctor_get(v_s_177_, 1);
lean_inc(v_out_179_);
lean_dec_ref(v_s_177_);
v___f_180_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1), 4, 3);
lean_closure_set(v___f_180_, 0, v_toPure_172_);
lean_closure_set(v___f_180_, 1, v_recur_173_);
lean_closure_set(v___f_180_, 2, v_it_178_);
v___x_181_ = lean_apply_3(v___y_174_, v_out_179_, lean_box(0), v_acc_175_);
v___x_182_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_181_, v___f_180_);
return v___x_182_;
}
case 1:
{
lean_object* v_it_183_; lean_object* v___x_184_; 
lean_dec(v_toBind_176_);
lean_dec(v___y_174_);
lean_dec(v_toPure_172_);
v_it_183_ = lean_ctor_get(v_s_177_, 0);
lean_inc(v_it_183_);
lean_dec_ref(v_s_177_);
v___x_184_ = lean_apply_4(v_recur_173_, v_it_183_, v_acc_175_, lean_box(0), lean_box(0));
return v___x_184_;
}
default: 
{
lean_object* v___x_185_; 
lean_dec(v_toBind_176_);
lean_dec(v___y_174_);
lean_dec(v_recur_173_);
v___x_185_ = lean_apply_2(v_toPure_172_, lean_box(0), v_acc_175_);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2(lean_object* v_inst_186_, lean_object* v_toPure_187_, lean_object* v___y_188_, lean_object* v_toBind_189_, lean_object* v_inst_190_, lean_object* v___f_191_, lean_object* v_lift_192_, lean_object* v_it_193_, lean_object* v_acc_194_, lean_object* v_hP_195_, lean_object* v_recur_196_){
_start:
{
lean_object* v_toApplicative_197_; lean_object* v_toFunctor_198_; lean_object* v_map_199_; lean_object* v___f_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_toApplicative_197_ = lean_ctor_get(v_inst_186_, 0);
lean_inc_ref(v_toApplicative_197_);
lean_dec_ref(v_inst_186_);
v_toFunctor_198_ = lean_ctor_get(v_toApplicative_197_, 0);
lean_inc_ref(v_toFunctor_198_);
lean_dec_ref(v_toApplicative_197_);
v_map_199_ = lean_ctor_get(v_toFunctor_198_, 0);
lean_inc(v_map_199_);
lean_dec_ref(v_toFunctor_198_);
v___f_200_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0), 6, 5);
lean_closure_set(v___f_200_, 0, v_toPure_187_);
lean_closure_set(v___f_200_, 1, v_recur_196_);
lean_closure_set(v___f_200_, 2, v___y_188_);
lean_closure_set(v___f_200_, 3, v_acc_194_);
lean_closure_set(v___f_200_, 4, v_toBind_189_);
v___x_201_ = lean_apply_1(v_inst_190_, v_it_193_);
v___x_202_ = lean_apply_4(v_map_199_, lean_box(0), lean_box(0), v___f_191_, v___x_201_);
v___x_203_ = lean_apply_4(v_lift_192_, lean_box(0), lean_box(0), v___f_200_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v___f_207_, lean_object* v_lift_208_, lean_object* v_00_u03b3_209_, lean_object* v_Pl_210_, lean_object* v_it_211_, lean_object* v_init_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_toApplicative_214_; lean_object* v_toBind_215_; lean_object* v_toPure_216_; lean_object* v___f_217_; lean_object* v___x_218_; 
v_toApplicative_214_ = lean_ctor_get(v_inst_204_, 0);
lean_inc_ref(v_toApplicative_214_);
v_toBind_215_ = lean_ctor_get(v_inst_204_, 1);
lean_inc(v_toBind_215_);
lean_dec_ref(v_inst_204_);
v_toPure_216_ = lean_ctor_get(v_toApplicative_214_, 1);
lean_inc(v_toPure_216_);
lean_dec_ref(v_toApplicative_214_);
v___f_217_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2), 11, 7);
lean_closure_set(v___f_217_, 0, v_inst_205_);
lean_closure_set(v___f_217_, 1, v_toPure_216_);
lean_closure_set(v___f_217_, 2, v___y_213_);
lean_closure_set(v___f_217_, 3, v_toBind_215_);
lean_closure_set(v___f_217_, 4, v_inst_206_);
lean_closure_set(v___f_217_, 5, v___f_207_);
lean_closure_set(v___f_217_, 6, v_lift_208_);
v___x_218_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_217_, v_it_211_, v_init_212_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___f_222_; lean_object* v___f_223_; 
v___f_222_ = ((lean_object*)(l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0));
v___f_223_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3), 10, 4);
lean_closure_set(v___f_223_, 0, v_inst_220_);
lean_closure_set(v___f_223_, 1, v_inst_219_);
lean_closure_set(v___f_223_, 2, v_inst_221_);
lean_closure_set(v___f_223_, 3, v___f_222_);
return v___f_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_m_226_, lean_object* v_inst_227_, lean_object* v_n_228_, lean_object* v_inst_229_, lean_object* v_P_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(v_inst_227_, v_inst_229_, v_inst_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg(lean_object* v_it_233_){
_start:
{
lean_inc(v_it_233_);
return v_it_233_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg___boxed(lean_object* v_it_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_IterM_attachWith___redArg(v_it_234_);
lean_dec(v_it_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_m_238_, lean_object* v_inst_239_, lean_object* v_inst_240_, lean_object* v_it_241_, lean_object* v_P_242_, lean_object* v_h_243_){
_start:
{
lean_inc(v_it_241_);
return v_it_241_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___boxed(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_m_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_it_249_, lean_object* v_P_250_, lean_object* v_h_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_IterM_attachWith(v_00_u03b1_244_, v_00_u03b2_245_, v_m_246_, v_inst_247_, v_inst_248_, v_it_249_, v_P_250_, v_h_251_);
lean_dec(v_it_249_);
lean_dec(v_inst_248_);
lean_dec_ref(v_inst_247_);
return v_res_252_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin);
}
#ifdef __cplusplus
}
#endif
