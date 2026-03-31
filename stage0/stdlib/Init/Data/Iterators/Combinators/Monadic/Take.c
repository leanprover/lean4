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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(lean_object* v_toApplicative_43_, lean_object* v_countdown_44_, lean_object* v___x_45_, lean_object* v_____do__lift_46_){
_start:
{
switch(lean_obj_tag(v_____do__lift_46_))
{
case 0:
{
lean_object* v_it_47_; lean_object* v_out_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_59_; 
v_it_47_ = lean_ctor_get(v_____do__lift_46_, 0);
v_out_48_ = lean_ctor_get(v_____do__lift_46_, 1);
v_isSharedCheck_59_ = !lean_is_exclusive(v_____do__lift_46_);
if (v_isSharedCheck_59_ == 0)
{
v___x_50_ = v_____do__lift_46_;
v_isShared_51_ = v_isSharedCheck_59_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_out_48_);
lean_inc(v_it_47_);
lean_dec(v_____do__lift_46_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_59_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v_toPure_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_56_; 
v_toPure_52_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_52_);
lean_dec_ref(v_toApplicative_43_);
v___x_53_ = lean_nat_sub(v_countdown_44_, v___x_45_);
lean_dec(v_countdown_44_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_it_47_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_54_);
v___x_56_ = v___x_50_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_54_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_out_48_);
v___x_56_ = v_reuseFailAlloc_58_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
lean_object* v___x_57_; 
v___x_57_ = lean_apply_2(v_toPure_52_, lean_box(0), v___x_56_);
return v___x_57_;
}
}
}
case 1:
{
lean_object* v_it_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_70_; 
v_it_60_ = lean_ctor_get(v_____do__lift_46_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v_____do__lift_46_);
if (v_isSharedCheck_70_ == 0)
{
v___x_62_ = v_____do__lift_46_;
v_isShared_63_ = v_isSharedCheck_70_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_it_60_);
lean_dec(v_____do__lift_46_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_70_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_toPure_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v_toPure_64_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_64_);
lean_dec_ref(v_toApplicative_43_);
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v_countdown_44_);
lean_ctor_set(v___x_65_, 1, v_it_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 0, v___x_65_);
v___x_67_ = v___x_62_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_69_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_68_; 
v___x_68_ = lean_apply_2(v_toPure_64_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
}
default: 
{
lean_object* v_toPure_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
lean_dec(v_countdown_44_);
v_toPure_71_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_71_);
lean_dec_ref(v_toApplicative_43_);
v___x_72_ = lean_box(2);
v___x_73_ = lean_apply_2(v_toPure_71_, lean_box(0), v___x_72_);
return v___x_73_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed(lean_object* v_toApplicative_74_, lean_object* v_countdown_75_, lean_object* v___x_76_, lean_object* v_____do__lift_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Std_Iterators_Types_Take_instIterator___redArg___lam__0(v_toApplicative_74_, v_countdown_75_, v___x_76_, v_____do__lift_77_);
lean_dec(v___x_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg___lam__1(lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_it_81_){
_start:
{
lean_object* v_countdown_82_; lean_object* v_inner_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_countdown_82_ = lean_ctor_get(v_it_81_, 0);
lean_inc(v_countdown_82_);
v_inner_83_ = lean_ctor_get(v_it_81_, 1);
lean_inc(v_inner_83_);
lean_dec_ref(v_it_81_);
v___x_84_ = lean_unsigned_to_nat(1u);
v___x_85_ = lean_nat_dec_eq(v_countdown_82_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v_toApplicative_86_; lean_object* v_toBind_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_toApplicative_86_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toApplicative_86_);
v_toBind_87_ = lean_ctor_get(v_inst_79_, 1);
lean_inc(v_toBind_87_);
lean_dec_ref(v_inst_79_);
v___f_88_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_88_, 0, v_toApplicative_86_);
lean_closure_set(v___f_88_, 1, v_countdown_82_);
lean_closure_set(v___f_88_, 2, v___x_84_);
v___x_89_ = lean_apply_1(v_inst_80_, v_inner_83_);
v___x_90_ = lean_apply_4(v_toBind_87_, lean_box(0), lean_box(0), v___x_89_, v___f_88_);
return v___x_90_;
}
else
{
lean_object* v_toApplicative_91_; lean_object* v_toPure_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_dec(v_inner_83_);
lean_dec(v_countdown_82_);
lean_dec(v_inst_80_);
v_toApplicative_91_ = lean_ctor_get(v_inst_79_, 0);
lean_inc_ref(v_toApplicative_91_);
lean_dec_ref(v_inst_79_);
v_toPure_92_ = lean_ctor_get(v_toApplicative_91_, 1);
lean_inc(v_toPure_92_);
lean_dec_ref(v_toApplicative_91_);
v___x_93_ = lean_box(2);
v___x_94_ = lean_apply_2(v_toPure_92_, lean_box(0), v___x_93_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator___redArg(lean_object* v_inst_95_, lean_object* v_inst_96_){
_start:
{
lean_object* v___f_97_; 
v___f_97_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_97_, 0, v_inst_95_);
lean_closure_set(v___f_97_, 1, v_inst_96_);
return v___f_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIterator(lean_object* v_00_u03b1_98_, lean_object* v_m_99_, lean_object* v_00_u03b2_100_, lean_object* v_inst_101_, lean_object* v_inst_102_){
_start:
{
lean_object* v___f_103_; 
v___f_103_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__1), 3, 2);
lean_closure_set(v___f_103_, 0, v_inst_101_);
lean_closure_set(v___f_103_, 1, v_inst_102_);
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
lean_dec_ref(v_____do__lift_121_);
v___x_123_ = lean_apply_2(v_toPure_118_, lean_box(0), v_a_122_);
return v___x_123_;
}
else
{
lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_toPure_118_);
v_a_124_ = lean_ctor_get(v_____do__lift_121_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v_____do__lift_121_);
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
lean_dec_ref(v_s_131_);
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
lean_dec_ref(v_s_131_);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3(lean_object* v_toPure_140_, lean_object* v___y_141_, lean_object* v_toBind_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_lift_145_, lean_object* v_it_146_, lean_object* v_acc_147_, lean_object* v_hP_148_, lean_object* v_recur_149_){
_start:
{
lean_object* v_countdown_150_; lean_object* v_inner_151_; lean_object* v___f_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_countdown_150_ = lean_ctor_get(v_it_146_, 0);
lean_inc(v_countdown_150_);
v_inner_151_ = lean_ctor_get(v_it_146_, 1);
lean_inc(v_inner_151_);
lean_dec_ref(v_it_146_);
v___f_152_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_152_, 0, v_toPure_140_);
lean_closure_set(v___f_152_, 1, v_recur_149_);
lean_closure_set(v___f_152_, 2, v___y_141_);
lean_closure_set(v___f_152_, 3, v_acc_147_);
lean_closure_set(v___f_152_, 4, v_toBind_142_);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_dec_eq(v_countdown_150_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v_toApplicative_155_; lean_object* v_toBind_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_toApplicative_155_ = lean_ctor_get(v_inst_143_, 0);
lean_inc_ref(v_toApplicative_155_);
v_toBind_156_ = lean_ctor_get(v_inst_143_, 1);
lean_inc(v_toBind_156_);
lean_dec_ref(v_inst_143_);
v___f_157_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIterator___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_157_, 0, v_toApplicative_155_);
lean_closure_set(v___f_157_, 1, v_countdown_150_);
lean_closure_set(v___f_157_, 2, v___x_153_);
v___x_158_ = lean_apply_1(v_inst_144_, v_inner_151_);
v___x_159_ = lean_apply_4(v_toBind_156_, lean_box(0), lean_box(0), v___x_158_, v___f_157_);
v___x_160_ = lean_apply_4(v_lift_145_, lean_box(0), lean_box(0), v___f_152_, v___x_159_);
return v___x_160_;
}
else
{
lean_object* v_toApplicative_161_; lean_object* v_toPure_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
lean_dec(v_inner_151_);
lean_dec(v_countdown_150_);
lean_dec(v_inst_144_);
v_toApplicative_161_ = lean_ctor_get(v_inst_143_, 0);
lean_inc_ref(v_toApplicative_161_);
lean_dec_ref(v_inst_143_);
v_toPure_162_ = lean_ctor_get(v_toApplicative_161_, 1);
lean_inc(v_toPure_162_);
lean_dec_ref(v_toApplicative_161_);
v___x_163_ = lean_box(2);
v___x_164_ = lean_apply_2(v_toPure_162_, lean_box(0), v___x_163_);
v___x_165_ = lean_apply_4(v_lift_145_, lean_box(0), lean_box(0), v___f_152_, v___x_164_);
return v___x_165_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_lift_169_, lean_object* v_00_u03b3_170_, lean_object* v_Pl_171_, lean_object* v_it_172_, lean_object* v_init_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v_toPure_177_; lean_object* v___f_178_; lean_object* v___x_179_; 
v_toApplicative_175_ = lean_ctor_get(v_inst_166_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_166_, 1);
lean_inc(v_toBind_176_);
lean_dec_ref(v_inst_166_);
v_toPure_177_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_177_);
lean_dec_ref(v_toApplicative_175_);
v___f_178_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__3), 10, 6);
lean_closure_set(v___f_178_, 0, v_toPure_177_);
lean_closure_set(v___f_178_, 1, v___y_174_);
lean_closure_set(v___f_178_, 2, v_toBind_176_);
lean_closure_set(v___f_178_, 3, v_inst_167_);
lean_closure_set(v___f_178_, 4, v_inst_168_);
lean_closure_set(v___f_178_, 5, v_lift_169_);
v___x_179_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_178_, v_it_172_, v_init_173_, lean_box(0));
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop___redArg(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_){
_start:
{
lean_object* v___f_183_; 
v___f_183_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_183_, 0, v_inst_181_);
lean_closure_set(v___f_183_, 1, v_inst_180_);
lean_closure_set(v___f_183_, 2, v_inst_182_);
return v___f_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Take_instIteratorLoop(lean_object* v_00_u03b1_184_, lean_object* v_m_185_, lean_object* v_00_u03b2_186_, lean_object* v_n_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___f_191_; 
v___f_191_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Take_instIteratorLoop___redArg___lam__2), 9, 3);
lean_closure_set(v___f_191_, 0, v_inst_189_);
lean_closure_set(v___f_191_, 1, v_inst_188_);
lean_closure_set(v___f_191_, 2, v_inst_190_);
return v___f_191_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Take(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
