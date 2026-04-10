// Lean compiler output
// Module: Lake.Util.Lift
// Imports: public import Init.System.IO
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
lean_object* l_EIO_toBaseIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_00_u03b1_2_){
_start:
{
lean_object* v_throw_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_throw_3_ = lean_ctor_get(v_inst_1_, 0);
lean_inc(v_throw_3_);
lean_dec_ref(v_inst_1_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_2(v_throw_3_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_00_u03b1_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v_tryCatch_10_; lean_object* v___x_11_; 
v_tryCatch_10_ = lean_ctor_get(v_inst_6_, 1);
lean_inc(v_tryCatch_10_);
lean_dec_ref(v_inst_6_);
v___x_11_ = lean_apply_3(v_tryCatch_10_, lean_box(0), v___y_8_, v___y_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_toApplicative_14_; lean_object* v___f_15_; lean_object* v___f_16_; lean_object* v___x_17_; 
v_toApplicative_14_ = lean_ctor_get(v_inst_12_, 0);
lean_inc_ref(v_inst_13_);
v___f_15_ = lean_alloc_closure((void*)(l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__0), 2, 1);
lean_closure_set(v___f_15_, 0, v_inst_13_);
v___f_16_ = lean_alloc_closure((void*)(l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___lam__1), 4, 1);
lean_closure_set(v___f_16_, 0, v_inst_13_);
lean_inc_ref(v_toApplicative_14_);
v___x_17_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_17_, 0, v_toApplicative_14_);
lean_ctor_set(v___x_17_, 1, v___f_15_);
lean_ctor_set(v___x_17_, 2, v___f_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg___boxed(lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_18_, v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(lean_object* v_m_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___redArg(v_inst_22_, v_inst_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake___boxed(lean_object* v_m_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_instAlternativeOfMonadOfMonadExceptOfPUnit__lake(v_m_25_, v_inst_26_, v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0(lean_object* v_inst_29_, lean_object* v_00_u03b1_30_, lean_object* v___y_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_2(v_inst_29_, lean_box(0), v___y_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake___redArg(lean_object* v_inst_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(v___f_34_, 0, v_inst_33_);
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOfMonadLift__lake(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___f_38_; 
v___f_38_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOfMonadLift__lake___redArg___lam__0), 3, 1);
lean_closure_set(v___f_38_, 0, v_inst_37_);
return v___f_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0(lean_object* v_inst_39_, lean_object* v_00_u03b1_40_, lean_object* v_act_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_apply_2(v_inst_39_, lean_box(0), v_act_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake___redArg(lean_object* v_inst_43_){
_start:
{
lean_object* v___f_44_; 
v___f_44_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0), 3, 1);
lean_closure_set(v___f_44_, 0, v_inst_43_);
return v___f_44_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTIdOfPure__lake(lean_object* v_m_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v___f_47_; 
v___f_47_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTIdOfPure__lake___redArg___lam__0), 3, 1);
lean_closure_set(v___f_47_, 0, v_inst_46_);
return v___f_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0(lean_object* v_failure_48_, lean_object* v_toPure_49_, lean_object* v_00_u03b1_50_, lean_object* v_x_51_){
_start:
{
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_52_; 
lean_dec(v_toPure_49_);
v___x_52_ = lean_apply_1(v_failure_48_, lean_box(0));
return v___x_52_;
}
else
{
lean_object* v_val_53_; lean_object* v___x_54_; 
lean_dec(v_failure_48_);
v_val_53_ = lean_ctor_get(v_x_51_, 0);
lean_inc(v_val_53_);
lean_dec_ref(v_x_51_);
v___x_54_ = lean_apply_2(v_toPure_49_, lean_box(0), v_val_53_);
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(lean_object* v_inst_55_){
_start:
{
lean_object* v_toApplicative_56_; lean_object* v_failure_57_; lean_object* v_toPure_58_; lean_object* v___f_59_; 
v_toApplicative_56_ = lean_ctor_get(v_inst_55_, 0);
lean_inc_ref(v_toApplicative_56_);
v_failure_57_ = lean_ctor_get(v_inst_55_, 1);
lean_inc(v_failure_57_);
lean_dec_ref(v_inst_55_);
v_toPure_58_ = lean_ctor_get(v_toApplicative_56_, 1);
lean_inc(v_toPure_58_);
lean_dec_ref(v_toApplicative_56_);
v___f_59_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg___lam__0), 4, 2);
lean_closure_set(v___f_59_, 0, v_failure_57_);
lean_closure_set(v___f_59_, 1, v_toPure_58_);
return v___f_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionOfAlternative__lake(lean_object* v_m_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_00_u03b1_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_throw_68_; lean_object* v___x_69_; 
lean_dec(v_inst_64_);
v_a_67_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v_x_66_);
v_throw_68_ = lean_ctor_get(v_inst_63_, 0);
lean_inc(v_throw_68_);
lean_dec_ref(v_inst_63_);
v___x_69_ = lean_apply_2(v_throw_68_, lean_box(0), v_a_67_);
return v___x_69_;
}
else
{
lean_object* v_a_70_; lean_object* v___x_71_; 
lean_dec_ref(v_inst_63_);
v_a_70_ = lean_ctor_get(v_x_66_, 0);
lean_inc(v_a_70_);
lean_dec_ref(v_x_66_);
v___x_71_ = lean_apply_2(v_inst_64_, lean_box(0), v_a_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg(lean_object* v_inst_72_, lean_object* v_inst_73_){
_start:
{
lean_object* v___f_74_; 
v___f_74_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(v___f_74_, 0, v_inst_73_);
lean_closure_set(v___f_74_, 1, v_inst_72_);
return v___f_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake(lean_object* v_m_75_, lean_object* v_00_u03b5_76_, lean_object* v_inst_77_, lean_object* v_inst_78_){
_start:
{
lean_object* v___f_79_; 
v___f_79_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(v___f_79_, 0, v_inst_78_);
lean_closure_set(v___f_79_, 1, v_inst_77_);
return v___f_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0(lean_object* v_act_80_, lean_object* v_inst_81_, lean_object* v_____do__lift_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_apply_1(v_act_80_, v_____do__lift_82_);
v___x_84_ = lean_apply_2(v_inst_81_, lean_box(0), v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1(lean_object* v_inst_85_, lean_object* v_toBind_86_, lean_object* v_inst_87_, lean_object* v_00_u03b1_88_, lean_object* v_act_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; 
v___f_90_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_act_89_);
lean_closure_set(v___f_90_, 1, v_inst_85_);
v___x_91_ = lean_apply_4(v_toBind_86_, lean_box(0), lean_box(0), v_inst_87_, v___f_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v_toBind_95_; lean_object* v___f_96_; 
v_toBind_95_ = lean_ctor_get(v_inst_92_, 1);
lean_inc(v_toBind_95_);
lean_dec_ref(v_inst_92_);
v___f_96_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg___lam__1), 5, 3);
lean_closure_set(v___f_96_, 0, v_inst_94_);
lean_closure_set(v___f_96_, 1, v_toBind_95_);
lean_closure_set(v___f_96_, 2, v_inst_93_);
return v___f_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake(lean_object* v_m_97_, lean_object* v_00_u03c1_98_, lean_object* v_n_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_inst_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lake_instMonadLiftTReaderTOfMonadOfMonadReaderOf__lake___redArg(v_inst_100_, v_inst_101_, v_inst_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0(lean_object* v_toPure_104_, lean_object* v_fst_105_, lean_object* v_____r_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_apply_2(v_toPure_104_, lean_box(0), v_fst_105_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1(lean_object* v_inst_108_, lean_object* v_toPure_109_, lean_object* v_toBind_110_, lean_object* v_____x_111_){
_start:
{
lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v_set_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_fst_112_ = lean_ctor_get(v_____x_111_, 0);
lean_inc(v_fst_112_);
v_snd_113_ = lean_ctor_get(v_____x_111_, 1);
lean_inc(v_snd_113_);
lean_dec_ref(v_____x_111_);
v_set_114_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_set_114_);
lean_dec_ref(v_inst_108_);
v___f_115_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__0), 3, 2);
lean_closure_set(v___f_115_, 0, v_toPure_109_);
lean_closure_set(v___f_115_, 1, v_fst_112_);
v___x_116_ = lean_apply_1(v_set_114_, v_snd_113_);
v___x_117_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_116_, v___f_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2(lean_object* v_act_118_, lean_object* v_inst_119_, lean_object* v_toBind_120_, lean_object* v___f_121_, lean_object* v_____do__lift_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_apply_1(v_act_118_, v_____do__lift_122_);
v___x_124_ = lean_apply_2(v_inst_119_, lean_box(0), v___x_123_);
v___x_125_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_124_, v___f_121_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_toBind_128_, lean_object* v___f_129_, lean_object* v_00_u03b1_130_, lean_object* v_act_131_){
_start:
{
lean_object* v_get_132_; lean_object* v___f_133_; lean_object* v___x_134_; 
v_get_132_ = lean_ctor_get(v_inst_126_, 0);
lean_inc(v_get_132_);
lean_dec_ref(v_inst_126_);
lean_inc(v_toBind_128_);
v___f_133_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__2), 5, 4);
lean_closure_set(v___f_133_, 0, v_act_131_);
lean_closure_set(v___f_133_, 1, v_inst_127_);
lean_closure_set(v___f_133_, 2, v_toBind_128_);
lean_closure_set(v___f_133_, 3, v___f_129_);
v___x_134_ = lean_apply_4(v_toBind_128_, lean_box(0), lean_box(0), v_get_132_, v___f_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_inst_137_){
_start:
{
lean_object* v_toApplicative_138_; lean_object* v_toBind_139_; lean_object* v_toPure_140_; lean_object* v___f_141_; lean_object* v___f_142_; 
v_toApplicative_138_ = lean_ctor_get(v_inst_135_, 0);
lean_inc_ref(v_toApplicative_138_);
v_toBind_139_ = lean_ctor_get(v_inst_135_, 1);
lean_inc_n(v_toBind_139_, 2);
lean_dec_ref(v_inst_135_);
v_toPure_140_ = lean_ctor_get(v_toApplicative_138_, 1);
lean_inc(v_toPure_140_);
lean_dec_ref(v_toApplicative_138_);
lean_inc_ref(v_inst_136_);
v___f_141_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__1), 4, 3);
lean_closure_set(v___f_141_, 0, v_inst_136_);
lean_closure_set(v___f_141_, 1, v_toPure_140_);
lean_closure_set(v___f_141_, 2, v_toBind_139_);
v___f_142_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg___lam__3), 6, 4);
lean_closure_set(v___f_142_, 0, v_inst_136_);
lean_closure_set(v___f_142_, 1, v_inst_137_);
lean_closure_set(v___f_142_, 2, v_toBind_139_);
lean_closure_set(v___f_142_, 3, v___f_141_);
return v___f_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake(lean_object* v_m_143_, lean_object* v_00_u03c3_144_, lean_object* v_n_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lake_instMonadLiftTStateTOfMonadOfMonadStateOf__lake___redArg(v_inst_146_, v_inst_147_, v_inst_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0(lean_object* v_inst_150_, lean_object* v___x_151_, lean_object* v_toBind_152_, lean_object* v_00_u03b1_153_, lean_object* v_act_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_apply_2(v_inst_150_, lean_box(0), v_act_154_);
v___x_156_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_156_, 0, lean_box(0));
lean_closure_set(v___x_156_, 1, lean_box(0));
lean_closure_set(v___x_156_, 2, v___x_151_);
lean_closure_set(v___x_156_, 3, lean_box(0));
v___x_157_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_inst_160_){
_start:
{
lean_object* v_toBind_161_; lean_object* v___x_162_; lean_object* v___f_163_; 
v_toBind_161_ = lean_ctor_get(v_inst_158_, 1);
lean_inc(v_toBind_161_);
lean_dec_ref(v_inst_158_);
v___x_162_ = l_Lake_instMonadLiftTOptionOfAlternative__lake___redArg(v_inst_159_);
v___f_163_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg___lam__0), 5, 3);
lean_closure_set(v___f_163_, 0, v_inst_160_);
lean_closure_set(v___f_163_, 1, v___x_162_);
lean_closure_set(v___f_163_, 2, v_toBind_161_);
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake(lean_object* v_m_164_, lean_object* v_n_165_, lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lake_instMonadLiftTOptionTOfMonadOfAlternative__lake___redArg(v_inst_166_, v_inst_167_, v_inst_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0(lean_object* v_inst_170_, lean_object* v___f_171_, lean_object* v_toBind_172_, lean_object* v_00_u03b1_173_, lean_object* v_act_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_apply_2(v_inst_170_, lean_box(0), v_act_174_);
v___x_176_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_176_, 0, lean_box(0));
lean_closure_set(v___x_176_, 1, lean_box(0));
lean_closure_set(v___x_176_, 2, v___f_171_);
lean_closure_set(v___x_176_, 3, lean_box(0));
v___x_177_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_inst_180_){
_start:
{
lean_object* v_toApplicative_181_; lean_object* v_toBind_182_; lean_object* v_toPure_183_; lean_object* v___f_184_; lean_object* v___f_185_; 
v_toApplicative_181_ = lean_ctor_get(v_inst_178_, 0);
lean_inc_ref(v_toApplicative_181_);
v_toBind_182_ = lean_ctor_get(v_inst_178_, 1);
lean_inc(v_toBind_182_);
lean_dec_ref(v_inst_178_);
v_toPure_183_ = lean_ctor_get(v_toApplicative_181_, 1);
lean_inc(v_toPure_183_);
lean_dec_ref(v_toApplicative_181_);
v___f_184_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(v___f_184_, 0, v_inst_179_);
lean_closure_set(v___f_184_, 1, v_toPure_183_);
v___f_185_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg___lam__0), 5, 3);
lean_closure_set(v___f_185_, 0, v_inst_180_);
lean_closure_set(v___f_185_, 1, v___f_184_);
lean_closure_set(v___f_185_, 2, v_toBind_182_);
return v___f_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake(lean_object* v_m_186_, lean_object* v_00_u03b5_187_, lean_object* v_n_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lake_instMonadLiftTExceptTOfMonadOfMonadExceptOf__lake___redArg(v_inst_189_, v_inst_190_, v_inst_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0(lean_object* v_inst_193_, lean_object* v___f_194_, lean_object* v_toBind_195_, lean_object* v_00_u03b1_196_, lean_object* v_act_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_198_ = lean_alloc_closure((void*)(l_EIO_toBaseIO___boxed), 4, 3);
lean_closure_set(v___x_198_, 0, lean_box(0));
lean_closure_set(v___x_198_, 1, lean_box(0));
lean_closure_set(v___x_198_, 2, v_act_197_);
v___x_199_ = lean_apply_2(v_inst_193_, lean_box(0), v___x_198_);
v___x_200_ = lean_alloc_closure((void*)(l_liftM), 5, 4);
lean_closure_set(v___x_200_, 0, lean_box(0));
lean_closure_set(v___x_200_, 1, lean_box(0));
lean_closure_set(v___x_200_, 2, v___f_194_);
lean_closure_set(v___x_200_, 3, lean_box(0));
v___x_201_ = lean_apply_4(v_toBind_195_, lean_box(0), lean_box(0), v___x_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v_toApplicative_205_; lean_object* v_toBind_206_; lean_object* v_toPure_207_; lean_object* v___f_208_; lean_object* v___f_209_; 
v_toApplicative_205_ = lean_ctor_get(v_inst_202_, 0);
lean_inc_ref(v_toApplicative_205_);
v_toBind_206_ = lean_ctor_get(v_inst_202_, 1);
lean_inc(v_toBind_206_);
lean_dec_ref(v_inst_202_);
v_toPure_207_ = lean_ctor_get(v_toApplicative_205_, 1);
lean_inc(v_toPure_207_);
lean_dec_ref(v_toApplicative_205_);
v___f_208_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTExceptOfPureOfMonadExceptOf__lake___redArg___lam__0), 4, 2);
lean_closure_set(v___f_208_, 0, v_inst_203_);
lean_closure_set(v___f_208_, 1, v_toPure_207_);
v___f_209_ = lean_alloc_closure((void*)(l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg___lam__0), 5, 3);
lean_closure_set(v___f_209_, 0, v_inst_204_);
lean_closure_set(v___f_209_, 1, v___f_208_);
lean_closure_set(v___f_209_, 2, v_toBind_206_);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake(lean_object* v_m_210_, lean_object* v_00_u03b5_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lake_instMonadLiftTEIOOfMonadOfMonadExceptOfOfBaseIO__lake___redArg(v_inst_212_, v_inst_213_, v_inst_214_);
return v___x_215_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Lift(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Lift(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Lift(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Lift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Lift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Lift(builtin);
}
#ifdef __cplusplus
}
#endif
