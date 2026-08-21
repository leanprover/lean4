// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.Take
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Loop public import Init.Classical import Init.ByCases import Init.Omega
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_take___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_take___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_take(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_take___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_toTake___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_take___redArg(lean_object* v_n_1_, lean_object* v_it_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_unsigned_to_nat(1u);
v___x_4_ = lean_nat_add(v_n_1_, v___x_3_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v_it_2_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_take___redArg___boxed(lean_object* v_n_6_, lean_object* v_it_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Std_IterM_take___redArg(v_n_6_, v_it_7_);
lean_dec(v_n_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_take(lean_object* v_00_u03b1_9_, lean_object* v_m_10_, lean_object* v_00_u03b2_11_, lean_object* v_inst_12_, lean_object* v_n_13_, lean_object* v_it_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = lean_nat_add(v_n_13_, v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_it_14_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_take___boxed(lean_object* v_00_u03b1_18_, lean_object* v_m_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_n_22_, lean_object* v_it_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_IterM_take(v_00_u03b1_18_, v_m_19_, v_00_u03b2_20_, v_inst_21_, v_n_22_, v_it_23_);
lean_dec(v_n_22_);
lean_dec(v_inst_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTake___redArg(lean_object* v_it_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v_it_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTake(lean_object* v_00_u03b1_28_, lean_object* v_m_29_, lean_object* v_00_u03b2_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_it_33_){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(0u);
v___x_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v_it_33_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_toTake___boxed(lean_object* v_00_u03b1_36_, lean_object* v_m_37_, lean_object* v_00_u03b2_38_, lean_object* v_inst_39_, lean_object* v_inst_40_, lean_object* v_it_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_IterM_toTake(v_00_u03b1_36_, v_m_37_, v_00_u03b2_38_, v_inst_39_, v_inst_40_, v_it_41_);
lean_dec(v_inst_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(lean_object* v_countdown_43_, lean_object* v___x_44_, lean_object* v_toPure_45_, lean_object* v_____do__lift_46_){
_start:
{
switch(lean_obj_tag(v_____do__lift_46_))
{
case 0:
{
lean_object* v_it_47_; lean_object* v_out_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_58_; 
v_it_47_ = lean_ctor_get(v_____do__lift_46_, 0);
v_out_48_ = lean_ctor_get(v_____do__lift_46_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v_____do__lift_46_);
if (v_isSharedCheck_58_ == 0)
{
v___x_50_ = v_____do__lift_46_;
v_isShared_51_ = v_isSharedCheck_58_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_out_48_);
lean_inc(v_it_47_);
lean_dec(v_____do__lift_46_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_58_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_52_ = lean_nat_sub(v_countdown_43_, v___x_44_);
lean_dec(v_countdown_43_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_it_47_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_53_);
v___x_55_ = v___x_50_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v___x_53_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_out_48_);
v___x_55_ = v_reuseFailAlloc_57_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; 
v___x_56_ = lean_apply_2(v_toPure_45_, lean_box(0), v___x_55_);
return v___x_56_;
}
}
}
case 1:
{
lean_object* v_it_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_68_; 
v_it_59_ = lean_ctor_get(v_____do__lift_46_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_____do__lift_46_);
if (v_isSharedCheck_68_ == 0)
{
v___x_61_ = v_____do__lift_46_;
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_it_59_);
lean_dec(v_____do__lift_46_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_68_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_63_, 0, v_countdown_43_);
lean_ctor_set(v___x_63_, 1, v_it_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_63_);
v___x_65_ = v___x_61_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_63_);
v___x_65_ = v_reuseFailAlloc_67_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_apply_2(v_toPure_45_, lean_box(0), v___x_65_);
return v___x_66_;
}
}
}
default: 
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_countdown_43_);
v___x_69_ = lean_box(2);
v___x_70_ = lean_apply_2(v_toPure_45_, lean_box(0), v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed(lean_object* v_countdown_71_, lean_object* v___x_72_, lean_object* v_toPure_73_, lean_object* v_____do__lift_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(v_countdown_71_, v___x_72_, v_toPure_73_, v_____do__lift_74_);
lean_dec(v___x_72_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(lean_object* v_toPure_76_, lean_object* v_inst_77_, lean_object* v_toBind_78_, lean_object* v_it_79_){
_start:
{
lean_object* v_countdown_80_; lean_object* v_inner_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v_countdown_80_ = lean_ctor_get(v_it_79_, 0);
lean_inc(v_countdown_80_);
v_inner_81_ = lean_ctor_get(v_it_79_, 1);
lean_inc(v_inner_81_);
lean_dec_ref(v_it_79_);
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_dec_eq(v_countdown_80_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___f_84_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_84_, 0, v_countdown_80_);
lean_closure_set(v___f_84_, 1, v___x_82_);
lean_closure_set(v___f_84_, 2, v_toPure_76_);
v___x_85_ = lean_apply_1(v_inst_77_, v_inner_81_);
v___x_86_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_85_, v___f_84_);
return v___x_86_;
}
else
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_inner_81_);
lean_dec(v_countdown_80_);
lean_dec(v_toBind_78_);
lean_dec(v_inst_77_);
v___x_87_ = lean_box(2);
v___x_88_ = lean_apply_2(v_toPure_76_, lean_box(0), v___x_87_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_){
_start:
{
lean_object* v_toApplicative_91_; lean_object* v_toBind_92_; lean_object* v_toPure_93_; lean_object* v___f_94_; 
v_toApplicative_91_ = lean_ctor_get(v_inst_89_, 0);
lean_inc_ref(v_toApplicative_91_);
v_toBind_92_ = lean_ctor_get(v_inst_89_, 1);
lean_inc(v_toBind_92_);
lean_dec_ref(v_inst_89_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc(v_toPure_93_);
lean_dec_ref(v_toApplicative_91_);
v___f_94_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_94_, 0, v_toPure_93_);
lean_closure_set(v___f_94_, 1, v_inst_90_);
lean_closure_set(v___f_94_, 2, v_toBind_92_);
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator(lean_object* v_00_u03b1_95_, lean_object* v_m_96_, lean_object* v_00_u03b2_97_, lean_object* v_inst_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v_toApplicative_100_; lean_object* v_toBind_101_; lean_object* v_toPure_102_; lean_object* v___f_103_; 
v_toApplicative_100_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_100_);
v_toBind_101_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_101_);
lean_dec_ref(v_inst_98_);
v_toPure_102_ = lean_ctor_get(v_toApplicative_100_, 1);
lean_inc(v_toPure_102_);
lean_dec_ref(v_toApplicative_100_);
v___f_103_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_103_, 0, v_toPure_102_);
lean_closure_set(v___f_103_, 1, v_inst_99_);
lean_closure_set(v___f_103_, 2, v_toBind_101_);
return v___f_103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(lean_object* v_00_u03b1_104_, lean_object* v_m_105_, lean_object* v_00_u03b2_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___boxed(lean_object* v_00_u03b1_111_, lean_object* v_m_112_, lean_object* v_00_u03b2_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(v_00_u03b1_111_, v_m_112_, v_00_u03b2_113_, v_inst_114_, v_inst_115_, v_inst_116_);
lean_dec(v_inst_115_);
lean_dec_ref(v_inst_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_118_, lean_object* v_recur_119_, lean_object* v_it_120_, lean_object* v_____do__lift_121_){
_start:
{
if (lean_obj_tag(v_____do__lift_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_123_; 
lean_dec_ref(v_it_120_);
lean_dec(v_recur_119_);
v_a_122_ = lean_ctor_get(v_____do__lift_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v_____do__lift_121_, 1);
v___x_123_ = lean_apply_2(v_toPure_118_, lean_box(0), v_a_122_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_toPure_118_);
v_a_124_ = lean_ctor_get(v_____do__lift_121_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v_____do__lift_121_, 1);
v___x_125_ = lean_apply_4(v_recur_119_, v_it_120_, v_a_124_, lean_box(0), lean_box(0));
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_126_, lean_object* v_recur_127_, lean_object* v___y_128_, lean_object* v_acc_129_, lean_object* v_toBind_130_, lean_object* v_s_131_){
_start:
{
switch(lean_obj_tag(v_s_131_))
{
case 0:
{
lean_object* v_it_132_; lean_object* v_out_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_it_132_ = lean_ctor_get(v_s_131_, 0);
lean_inc(v_it_132_);
v_out_133_ = lean_ctor_get(v_s_131_, 1);
lean_inc(v_out_133_);
lean_dec_ref_known(v_s_131_, 2);
v___f_134_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_134_, 0, v_toPure_126_);
lean_closure_set(v___f_134_, 1, v_recur_127_);
lean_closure_set(v___f_134_, 2, v_it_132_);
v___x_135_ = lean_apply_3(v___y_128_, v_out_133_, lean_box(0), v_acc_129_);
v___x_136_ = lean_apply_4(v_toBind_130_, lean_box(0), lean_box(0), v___x_135_, v___f_134_);
return v___x_136_;
}
case 1:
{
lean_object* v_it_137_; lean_object* v___x_138_; 
lean_dec(v_toBind_130_);
lean_dec(v___y_128_);
lean_dec(v_toPure_126_);
v_it_137_ = lean_ctor_get(v_s_131_, 0);
lean_inc(v_it_137_);
lean_dec_ref_known(v_s_131_, 1);
v___x_138_ = lean_apply_4(v_recur_127_, v_it_137_, v_acc_129_, lean_box(0), lean_box(0));
return v___x_138_;
}
default: 
{
lean_object* v___x_139_; 
lean_dec(v_toBind_130_);
lean_dec(v___y_128_);
lean_dec(v_recur_127_);
v___x_139_ = lean_apply_2(v_toPure_126_, lean_box(0), v_acc_129_);
return v___x_139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(lean_object* v_inst_140_, lean_object* v_toPure_141_, lean_object* v___y_142_, lean_object* v_toBind_143_, lean_object* v_inst_144_, lean_object* v_lift_145_, lean_object* v_it_146_, lean_object* v_acc_147_, lean_object* v_hP_148_, lean_object* v_recur_149_){
_start:
{
lean_object* v_toApplicative_150_; lean_object* v_toBind_151_; lean_object* v_toPure_152_; lean_object* v_countdown_153_; lean_object* v_inner_154_; lean_object* v___f_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_toApplicative_150_ = lean_ctor_get(v_inst_140_, 0);
lean_inc_ref(v_toApplicative_150_);
v_toBind_151_ = lean_ctor_get(v_inst_140_, 1);
lean_inc(v_toBind_151_);
lean_dec_ref(v_inst_140_);
v_toPure_152_ = lean_ctor_get(v_toApplicative_150_, 1);
lean_inc(v_toPure_152_);
lean_dec_ref(v_toApplicative_150_);
v_countdown_153_ = lean_ctor_get(v_it_146_, 0);
lean_inc(v_countdown_153_);
v_inner_154_ = lean_ctor_get(v_it_146_, 1);
lean_inc(v_inner_154_);
lean_dec_ref(v_it_146_);
v___f_155_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_155_, 0, v_toPure_141_);
lean_closure_set(v___f_155_, 1, v_recur_149_);
lean_closure_set(v___f_155_, 2, v___y_142_);
lean_closure_set(v___f_155_, 3, v_acc_147_);
lean_closure_set(v___f_155_, 4, v_toBind_143_);
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_dec_eq(v_countdown_153_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___f_158_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_158_, 0, v_countdown_153_);
lean_closure_set(v___f_158_, 1, v___x_156_);
lean_closure_set(v___f_158_, 2, v_toPure_152_);
v___x_159_ = lean_apply_1(v_inst_144_, v_inner_154_);
v___x_160_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_159_, v___f_158_);
v___x_161_ = lean_apply_4(v_lift_145_, lean_box(0), lean_box(0), v___f_155_, v___x_160_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_inner_154_);
lean_dec(v_countdown_153_);
lean_dec(v_toBind_151_);
lean_dec(v_inst_144_);
v___x_162_ = lean_box(2);
v___x_163_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_162_);
v___x_164_ = lean_apply_4(v_lift_145_, lean_box(0), lean_box(0), v___f_155_, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_lift_168_, lean_object* v_00_u03b3_169_, lean_object* v_Pl_170_, lean_object* v_it_171_, lean_object* v_init_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_toApplicative_174_; lean_object* v_toBind_175_; lean_object* v_toPure_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
v_toApplicative_174_ = lean_ctor_get(v_inst_165_, 0);
lean_inc_ref(v_toApplicative_174_);
v_toBind_175_ = lean_ctor_get(v_inst_165_, 1);
lean_inc(v_toBind_175_);
lean_dec_ref(v_inst_165_);
v_toPure_176_ = lean_ctor_get(v_toApplicative_174_, 1);
lean_inc(v_toPure_176_);
lean_dec_ref(v_toApplicative_174_);
v___f_177_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_177_, 0, v_inst_166_);
lean_closure_set(v___f_177_, 1, v_toPure_176_);
lean_closure_set(v___f_177_, 2, v___y_173_);
lean_closure_set(v___f_177_, 3, v_toBind_175_);
lean_closure_set(v___f_177_, 4, v_inst_167_);
lean_closure_set(v___f_177_, 5, v_lift_168_);
v___x_178_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_177_, v_it_171_, v_init_172_, lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg(lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_inst_181_){
_start:
{
lean_object* v___f_182_; 
v___f_182_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_182_, 0, v_inst_180_);
lean_closure_set(v___f_182_, 1, v_inst_179_);
lean_closure_set(v___f_182_, 2, v_inst_181_);
return v___f_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop(lean_object* v_00_u03b1_183_, lean_object* v_m_184_, lean_object* v_00_u03b2_185_, lean_object* v_n_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_){
_start:
{
lean_object* v___f_190_; 
v___f_190_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_190_, 0, v_inst_188_);
lean_closure_set(v___f_190_, 1, v_inst_187_);
lean_closure_set(v___f_190_, 2, v_inst_189_);
return v___f_190_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Monadic_Take(builtin);
}
#ifdef __cplusplus
}
#endif
