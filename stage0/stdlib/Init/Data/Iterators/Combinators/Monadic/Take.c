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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_box(0);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___redArg();
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(lean_object* v_00_u03b1_108_, lean_object* v_m_109_, lean_object* v_00_u03b2_110_, lean_object* v_inst_111_, lean_object* v_inst_112_, lean_object* v_inst_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(0);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation___boxed(lean_object* v_00_u03b1_115_, lean_object* v_m_116_, lean_object* v_00_u03b2_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Init_Data_Iterators_Combinators_Monadic_Take_0__Std_Iterators_Types_Take_instFinitenessRelation(v_00_u03b1_115_, v_m_116_, v_00_u03b2_117_, v_inst_118_, v_inst_119_, v_inst_120_);
lean_dec(v_inst_119_);
lean_dec_ref(v_inst_118_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_122_, lean_object* v_recur_123_, lean_object* v_it_124_, lean_object* v_____do__lift_125_){
_start:
{
if (lean_obj_tag(v_____do__lift_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; 
lean_dec_ref(v_it_124_);
lean_dec(v_recur_123_);
v_a_126_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_127_ = lean_apply_2(v_toPure_122_, lean_box(0), v_a_126_);
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; 
lean_dec(v_toPure_122_);
v_a_128_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_129_ = lean_apply_4(v_recur_123_, v_it_124_, v_a_128_, lean_box(0), lean_box(0));
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_130_, lean_object* v_recur_131_, lean_object* v___y_132_, lean_object* v_acc_133_, lean_object* v_toBind_134_, lean_object* v_s_135_){
_start:
{
switch(lean_obj_tag(v_s_135_))
{
case 0:
{
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_it_136_ = lean_ctor_get(v_s_135_, 0);
lean_inc(v_it_136_);
v_out_137_ = lean_ctor_get(v_s_135_, 1);
lean_inc(v_out_137_);
lean_dec_ref_known(v_s_135_, 2);
v___f_138_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_138_, 0, v_toPure_130_);
lean_closure_set(v___f_138_, 1, v_recur_131_);
lean_closure_set(v___f_138_, 2, v_it_136_);
v___x_139_ = lean_apply_3(v___y_132_, v_out_137_, lean_box(0), v_acc_133_);
v___x_140_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_139_, v___f_138_);
return v___x_140_;
}
case 1:
{
lean_object* v_it_141_; lean_object* v___x_142_; 
lean_dec(v_toBind_134_);
lean_dec(v___y_132_);
lean_dec(v_toPure_130_);
v_it_141_ = lean_ctor_get(v_s_135_, 0);
lean_inc(v_it_141_);
lean_dec_ref_known(v_s_135_, 1);
v___x_142_ = lean_apply_4(v_recur_131_, v_it_141_, v_acc_133_, lean_box(0), lean_box(0));
return v___x_142_;
}
default: 
{
lean_object* v___x_143_; 
lean_dec(v_toBind_134_);
lean_dec(v___y_132_);
lean_dec(v_recur_131_);
v___x_143_ = lean_apply_2(v_toPure_130_, lean_box(0), v_acc_133_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(lean_object* v_inst_144_, lean_object* v_toPure_145_, lean_object* v___y_146_, lean_object* v_toBind_147_, lean_object* v_inst_148_, lean_object* v_lift_149_, lean_object* v_it_150_, lean_object* v_acc_151_, lean_object* v_hP_152_, lean_object* v_recur_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toBind_155_; lean_object* v_toPure_156_; lean_object* v_countdown_157_; lean_object* v_inner_158_; lean_object* v___f_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_154_);
v_toBind_155_ = lean_ctor_get(v_inst_144_, 1);
lean_inc(v_toBind_155_);
lean_dec_ref(v_inst_144_);
v_toPure_156_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_inc(v_toPure_156_);
lean_dec_ref(v_toApplicative_154_);
v_countdown_157_ = lean_ctor_get(v_it_150_, 0);
lean_inc(v_countdown_157_);
v_inner_158_ = lean_ctor_get(v_it_150_, 1);
lean_inc(v_inner_158_);
lean_dec_ref(v_it_150_);
v___f_159_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_159_, 0, v_toPure_145_);
lean_closure_set(v___f_159_, 1, v_recur_153_);
lean_closure_set(v___f_159_, 2, v___y_146_);
lean_closure_set(v___f_159_, 3, v_acc_151_);
lean_closure_set(v___f_159_, 4, v_toBind_147_);
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_nat_dec_eq(v_countdown_157_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___f_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___f_162_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_162_, 0, v_countdown_157_);
lean_closure_set(v___f_162_, 1, v___x_160_);
lean_closure_set(v___f_162_, 2, v_toPure_156_);
v___x_163_ = lean_apply_1(v_inst_148_, v_inner_158_);
v___x_164_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v___x_163_, v___f_162_);
v___x_165_ = lean_apply_4(v_lift_149_, lean_box(0), lean_box(0), v___f_159_, v___x_164_);
return v___x_165_;
}
else
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v_inner_158_);
lean_dec(v_countdown_157_);
lean_dec(v_toBind_155_);
lean_dec(v_inst_148_);
v___x_166_ = lean_box(2);
v___x_167_ = lean_apply_2(v_toPure_156_, lean_box(0), v___x_166_);
v___x_168_ = lean_apply_4(v_lift_149_, lean_box(0), lean_box(0), v___f_159_, v___x_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_lift_172_, lean_object* v_00_u03b3_173_, lean_object* v_Pl_174_, lean_object* v_it_175_, lean_object* v_init_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_toApplicative_178_; lean_object* v_toBind_179_; lean_object* v_toPure_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
v_toApplicative_178_ = lean_ctor_get(v_inst_169_, 0);
lean_inc_ref(v_toApplicative_178_);
v_toBind_179_ = lean_ctor_get(v_inst_169_, 1);
lean_inc(v_toBind_179_);
lean_dec_ref(v_inst_169_);
v_toPure_180_ = lean_ctor_get(v_toApplicative_178_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_178_);
v___f_181_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_181_, 0, v_inst_170_);
lean_closure_set(v___f_181_, 1, v_toPure_180_);
lean_closure_set(v___f_181_, 2, v___y_177_);
lean_closure_set(v___f_181_, 3, v_toBind_179_);
lean_closure_set(v___f_181_, 4, v_inst_171_);
lean_closure_set(v___f_181_, 5, v_lift_172_);
v___x_182_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_181_, v_it_175_, v_init_176_, lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg(lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_){
_start:
{
lean_object* v___f_186_; 
v___f_186_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_186_, 0, v_inst_184_);
lean_closure_set(v___f_186_, 1, v_inst_183_);
lean_closure_set(v___f_186_, 2, v_inst_185_);
return v___f_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop(lean_object* v_00_u03b1_187_, lean_object* v_m_188_, lean_object* v_00_u03b2_189_, lean_object* v_n_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v___f_194_; 
v___f_194_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_194_, 0, v_inst_192_);
lean_closure_set(v___f_194_, 1, v_inst_191_);
lean_closure_set(v___f_194_, 2, v_inst_193_);
return v___f_194_;
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
