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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Iterators_Types_Attach_instFinitenessRelation___redArg();
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_m_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_, lean_object* v_P_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instFinitenessRelation___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_P_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Iterators_Types_Attach_instFinitenessRelation(v_00_u03b1_105_, v_00_u03b2_106_, v_m_107_, v_inst_108_, v_inst_109_, v_inst_110_, v_P_111_);
lean_dec(v_inst_109_);
lean_dec_ref(v_inst_108_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Iterators_Types_Attach_instProductivenessRelation___redArg();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_m_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_P_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(0);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instProductivenessRelation___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_m_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_P_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Iterators_Types_Attach_instProductivenessRelation(v_00_u03b1_125_, v_00_u03b2_126_, v_m_127_, v_inst_128_, v_inst_129_, v_inst_130_, v_P_131_);
lean_dec(v_inst_129_);
lean_dec_ref(v_inst_128_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_133_, lean_object* v_recur_134_, lean_object* v_it_135_, lean_object* v_____do__lift_136_){
_start:
{
if (lean_obj_tag(v_____do__lift_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
lean_dec(v_it_135_);
lean_dec(v_recur_134_);
v_a_137_ = lean_ctor_get(v_____do__lift_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v_____do__lift_136_, 1);
v___x_138_ = lean_apply_2(v_toPure_133_, lean_box(0), v_a_137_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_140_; 
lean_dec(v_toPure_133_);
v_a_139_ = lean_ctor_get(v_____do__lift_136_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v_____do__lift_136_, 1);
v___x_140_ = lean_apply_4(v_recur_134_, v_it_135_, v_a_139_, lean_box(0), lean_box(0));
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_141_, lean_object* v_recur_142_, lean_object* v___y_143_, lean_object* v_acc_144_, lean_object* v_toBind_145_, lean_object* v_s_146_){
_start:
{
switch(lean_obj_tag(v_s_146_))
{
case 0:
{
lean_object* v_it_147_; lean_object* v_out_148_; lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_it_147_ = lean_ctor_get(v_s_146_, 0);
lean_inc(v_it_147_);
v_out_148_ = lean_ctor_get(v_s_146_, 1);
lean_inc(v_out_148_);
lean_dec_ref_known(v_s_146_, 2);
v___f_149_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__1), 4, 3);
lean_closure_set(v___f_149_, 0, v_toPure_141_);
lean_closure_set(v___f_149_, 1, v_recur_142_);
lean_closure_set(v___f_149_, 2, v_it_147_);
v___x_150_ = lean_apply_3(v___y_143_, v_out_148_, lean_box(0), v_acc_144_);
v___x_151_ = lean_apply_4(v_toBind_145_, lean_box(0), lean_box(0), v___x_150_, v___f_149_);
return v___x_151_;
}
case 1:
{
lean_object* v_it_152_; lean_object* v___x_153_; 
lean_dec(v_toBind_145_);
lean_dec(v___y_143_);
lean_dec(v_toPure_141_);
v_it_152_ = lean_ctor_get(v_s_146_, 0);
lean_inc(v_it_152_);
lean_dec_ref_known(v_s_146_, 1);
v___x_153_ = lean_apply_4(v_recur_142_, v_it_152_, v_acc_144_, lean_box(0), lean_box(0));
return v___x_153_;
}
default: 
{
lean_object* v___x_154_; 
lean_dec(v_toBind_145_);
lean_dec(v___y_143_);
lean_dec(v_recur_142_);
v___x_154_ = lean_apply_2(v_toPure_141_, lean_box(0), v_acc_144_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2(lean_object* v_inst_155_, lean_object* v_toPure_156_, lean_object* v___y_157_, lean_object* v_toBind_158_, lean_object* v_inst_159_, lean_object* v___f_160_, lean_object* v_lift_161_, lean_object* v_it_162_, lean_object* v_acc_163_, lean_object* v_hP_164_, lean_object* v_recur_165_){
_start:
{
lean_object* v_toApplicative_166_; lean_object* v_toFunctor_167_; lean_object* v_map_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_toApplicative_166_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toApplicative_166_);
lean_dec_ref(v_inst_155_);
v_toFunctor_167_ = lean_ctor_get(v_toApplicative_166_, 0);
lean_inc_ref(v_toFunctor_167_);
lean_dec_ref(v_toApplicative_166_);
v_map_168_ = lean_ctor_get(v_toFunctor_167_, 0);
lean_inc(v_map_168_);
lean_dec_ref(v_toFunctor_167_);
v___f_169_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__0), 6, 5);
lean_closure_set(v___f_169_, 0, v_toPure_156_);
lean_closure_set(v___f_169_, 1, v_recur_165_);
lean_closure_set(v___f_169_, 2, v___y_157_);
lean_closure_set(v___f_169_, 3, v_acc_163_);
lean_closure_set(v___f_169_, 4, v_toBind_158_);
v___x_170_ = lean_apply_1(v_inst_159_, v_it_162_);
v___x_171_ = lean_apply_4(v_map_168_, lean_box(0), lean_box(0), v___f_160_, v___x_170_);
v___x_172_ = lean_apply_4(v_lift_161_, lean_box(0), lean_box(0), v___f_169_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v___f_176_, lean_object* v_lift_177_, lean_object* v_00_u03b3_178_, lean_object* v_Pl_179_, lean_object* v_it_180_, lean_object* v_init_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_toApplicative_183_; lean_object* v_toBind_184_; lean_object* v_toPure_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v_toApplicative_183_ = lean_ctor_get(v_inst_173_, 0);
lean_inc_ref(v_toApplicative_183_);
v_toBind_184_ = lean_ctor_get(v_inst_173_, 1);
lean_inc(v_toBind_184_);
lean_dec_ref(v_inst_173_);
v_toPure_185_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_inc(v_toPure_185_);
lean_dec_ref(v_toApplicative_183_);
v___f_186_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__2), 11, 7);
lean_closure_set(v___f_186_, 0, v_inst_174_);
lean_closure_set(v___f_186_, 1, v_toPure_185_);
lean_closure_set(v___f_186_, 2, v___y_182_);
lean_closure_set(v___f_186_, 3, v_toBind_184_);
lean_closure_set(v___f_186_, 4, v_inst_175_);
lean_closure_set(v___f_186_, 5, v___f_176_);
lean_closure_set(v___f_186_, 6, v_lift_177_);
v___x_187_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_186_, v_it_180_, v_init_181_, lean_box(0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; lean_object* v___f_192_; 
v___f_191_ = ((lean_object*)(l_Std_Iterators_Types_Attach_instIterator___redArg___closed__0));
v___f_192_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Attach_instIteratorLoop___redArg___lam__3), 10, 4);
lean_closure_set(v___f_192_, 0, v_inst_189_);
lean_closure_set(v___f_192_, 1, v_inst_188_);
lean_closure_set(v___f_192_, 2, v_inst_190_);
lean_closure_set(v___f_192_, 3, v___f_191_);
return v___f_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Attach_instIteratorLoop(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_n_197_, lean_object* v_inst_198_, lean_object* v_P_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_Iterators_Types_Attach_instIteratorLoop___redArg(v_inst_196_, v_inst_198_, v_inst_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg(lean_object* v_it_202_){
_start:
{
lean_inc(v_it_202_);
return v_it_202_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___redArg___boxed(lean_object* v_it_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Std_IterM_attachWith___redArg(v_it_203_);
lean_dec(v_it_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_m_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_it_210_, lean_object* v_P_211_, lean_object* v_h_212_){
_start:
{
lean_inc(v_it_210_);
return v_it_210_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_attachWith___boxed(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_m_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_it_218_, lean_object* v_P_219_, lean_object* v_h_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_IterM_attachWith(v_00_u03b1_213_, v_00_u03b2_214_, v_m_215_, v_inst_216_, v_inst_217_, v_it_218_, v_P_219_, v_h_220_);
lean_dec(v_it_218_);
lean_dec(v_inst_217_);
lean_dec_ref(v_inst_216_);
return v_res_221_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
