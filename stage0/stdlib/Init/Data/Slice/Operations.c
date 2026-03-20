// Lean compiler output
// Module: Init.Data.Slice.Operations
// Imports: public import Init.Data.Slice.Basic public import Init.Data.Iterators.ToIterator public import Init.Data.Iterators.Consumers.Loop import Init.Data.Iterators.Consumers.Collect
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
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_Internal_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_Internal_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_size___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Slice_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Slice_toArray___redArg___closed__0 = (const lean_object*)&l_Std_Slice_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Slice_toArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toListRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toListRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0 = (const lean_object*)&l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Slice_foldlM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Slice_foldlM___redArg___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Slice_foldlM___redArg___closed__0 = (const lean_object*)&l_Std_Slice_foldlM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldl___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_x_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_inst_1_, v_x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator___redArg(lean_object* v_inst_4_){
_start:
{
lean_object* v___f_5_; 
v___f_5_ = lean_alloc_closure((void*)(l_Std_Slice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_5_, 0, v_inst_4_);
return v___f_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instToIterator(lean_object* v_00_u03b3_6_, lean_object* v_m_7_, lean_object* v_00_u03b1_8_, lean_object* v_00_u03b2_9_, lean_object* v_inst_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = lean_alloc_closure((void*)(l_Std_Slice_instToIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_11_, 0, v_inst_10_);
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_Internal_iter___redArg(lean_object* v_inst_12_, lean_object* v_s_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_1(v_inst_12_, v_s_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_Internal_iter(lean_object* v_00_u03b3_15_, lean_object* v_00_u03b1_16_, lean_object* v_00_u03b2_17_, lean_object* v_inst_18_, lean_object* v_s_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_apply_1(v_inst_18_, v_s_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_size___redArg(lean_object* v_s_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_1(v_inst_22_, v_s_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_size(lean_object* v_00_u03b3_24_, lean_object* v_s_25_, lean_object* v_inst_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_1(v_inst_26_, v_s_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toArray___redArg___lam__0(lean_object* v_inst_28_, lean_object* v_it_29_, lean_object* v_acc_30_, lean_object* v_recur_31_){
_start:
{
lean_object* v_val_32_; 
v_val_32_ = lean_apply_1(v_inst_28_, v_it_29_);
switch(lean_obj_tag(v_val_32_))
{
case 0:
{
lean_object* v_it_33_; lean_object* v_out_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_it_33_ = lean_ctor_get(v_val_32_, 0);
lean_inc(v_it_33_);
v_out_34_ = lean_ctor_get(v_val_32_, 1);
lean_inc(v_out_34_);
lean_dec_ref(v_val_32_);
v___x_35_ = lean_array_push(v_acc_30_, v_out_34_);
v___x_36_ = lean_apply_3(v_recur_31_, v_it_33_, v___x_35_, lean_box(0));
return v___x_36_;
}
case 1:
{
lean_object* v_it_37_; lean_object* v___x_38_; 
v_it_37_ = lean_ctor_get(v_val_32_, 0);
lean_inc(v_it_37_);
lean_dec_ref(v_val_32_);
v___x_38_ = lean_apply_3(v_recur_31_, v_it_37_, v_acc_30_, lean_box(0));
return v___x_38_;
}
default: 
{
lean_dec_ref(v_recur_31_);
return v_acc_30_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toArray___redArg(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_s_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = lean_alloc_closure((void*)(l_Std_Slice_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_44_, 0, v_inst_42_);
v___x_45_ = lean_apply_1(v_inst_41_, v_s_43_);
v___x_46_ = ((lean_object*)(l_Std_Slice_toArray___redArg___closed__0));
v___x_47_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_44_, v___x_45_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toArray(lean_object* v_00_u03b3_48_, lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_s_53_){
_start:
{
lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___f_54_ = lean_alloc_closure((void*)(l_Std_Slice_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_54_, 0, v_inst_52_);
v___x_55_ = lean_apply_1(v_inst_51_, v_s_53_);
v___x_56_ = ((lean_object*)(l_Std_Slice_toArray___redArg___closed__0));
v___x_57_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toList___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_s_60_){
_start:
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___f_61_ = lean_alloc_closure((void*)(l_Std_Slice_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_61_, 0, v_inst_59_);
v___x_62_ = lean_apply_1(v_inst_58_, v_s_60_);
v___x_63_ = ((lean_object*)(l_Std_Slice_toArray___redArg___closed__0));
v___x_64_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_61_, v___x_62_, v___x_63_);
v___x_65_ = lean_array_to_list(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toList(lean_object* v_00_u03b3_66_, lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_s_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___f_72_ = lean_alloc_closure((void*)(l_Std_Slice_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_72_, 0, v_inst_70_);
v___x_73_ = lean_apply_1(v_inst_69_, v_s_71_);
v___x_74_ = ((lean_object*)(l_Std_Slice_toArray___redArg___closed__0));
v___x_75_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_72_, v___x_73_, v___x_74_);
v___x_76_ = lean_array_to_list(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toListRev___redArg___lam__0(lean_object* v_inst_77_, lean_object* v_it_78_, lean_object* v_acc_79_, lean_object* v_recur_80_){
_start:
{
lean_object* v_val_81_; 
v_val_81_ = lean_apply_1(v_inst_77_, v_it_78_);
switch(lean_obj_tag(v_val_81_))
{
case 0:
{
lean_object* v_it_82_; lean_object* v_out_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_it_82_ = lean_ctor_get(v_val_81_, 0);
v_out_83_ = lean_ctor_get(v_val_81_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_val_81_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_val_81_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_out_83_);
lean_inc(v_it_82_);
lean_dec(v_val_81_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 1);
lean_ctor_set(v___x_85_, 1, v_acc_79_);
lean_ctor_set(v___x_85_, 0, v_out_83_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_out_83_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_acc_79_);
v___x_88_ = v_reuseFailAlloc_90_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_3(v_recur_80_, v_it_82_, v___x_88_, lean_box(0));
return v___x_89_;
}
}
}
case 1:
{
lean_object* v_it_92_; lean_object* v___x_93_; 
v_it_92_ = lean_ctor_get(v_val_81_, 0);
lean_inc(v_it_92_);
lean_dec_ref(v_val_81_);
v___x_93_ = lean_apply_3(v_recur_80_, v_it_92_, v_acc_79_, lean_box(0));
return v___x_93_;
}
default: 
{
lean_dec_ref(v_recur_80_);
return v_acc_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toListRev___redArg(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_s_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___f_97_ = lean_alloc_closure((void*)(l_Std_Slice_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_97_, 0, v_inst_95_);
v___x_98_ = lean_apply_1(v_inst_94_, v_s_96_);
v___x_99_ = lean_box(0);
v___x_100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_97_, v___x_98_, v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_toListRev(lean_object* v_00_u03b3_101_, lean_object* v_00_u03b1_102_, lean_object* v_00_u03b2_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_s_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___f_107_ = lean_alloc_closure((void*)(l_Std_Slice_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_107_, 0, v_inst_105_);
v___x_108_ = lean_apply_1(v_inst_104_, v_s_106_);
v___x_109_ = lean_box(0);
v___x_110_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__0(lean_object* v_x_111_, lean_object* v_x_112_, lean_object* v_f_113_, lean_object* v_c_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_apply_1(v_f_113_, v_c_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1(lean_object* v_toPure_116_, lean_object* v_____do__lift_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_apply_2(v_toPure_116_, lean_box(0), v_____do__lift_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2(lean_object* v_f_119_, lean_object* v_toBind_120_, lean_object* v___f_121_, lean_object* v_x1_122_, lean_object* v_x2_123_, lean_object* v_x3_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_apply_2(v_f_119_, v_x1_122_, v_x3_124_);
v___x_126_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_125_, v___f_121_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3(lean_object* v_inst_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v___f_130_, lean_object* v_00_u03b2_131_, lean_object* v_s_132_, lean_object* v_init_133_, lean_object* v_f_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toBind_136_; lean_object* v_toPure_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___f_140_; lean_object* v___x_141_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_127_, 0);
lean_inc_ref(v_toApplicative_135_);
v_toBind_136_ = lean_ctor_get(v_inst_127_, 1);
lean_inc(v_toBind_136_);
lean_dec_ref(v_inst_127_);
v_toPure_137_ = lean_ctor_get(v_toApplicative_135_, 1);
lean_inc(v_toPure_137_);
lean_dec_ref(v_toApplicative_135_);
v___x_138_ = lean_apply_1(v_inst_128_, v_s_132_);
v___f_139_ = lean_alloc_closure((void*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1), 2, 1);
lean_closure_set(v___f_139_, 0, v_toPure_137_);
v___f_140_ = lean_alloc_closure((void*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__2), 6, 3);
lean_closure_set(v___f_140_, 0, v_f_134_);
lean_closure_set(v___f_140_, 1, v_toBind_136_);
lean_closure_set(v___f_140_, 2, v___f_139_);
v___x_141_ = lean_apply_6(v_inst_129_, v___f_130_, lean_box(0), lean_box(0), v___x_138_, v_init_133_, v___f_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_inst_145_){
_start:
{
lean_object* v___f_146_; lean_object* v___f_147_; 
v___f_146_ = ((lean_object*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0));
v___f_147_ = lean_alloc_closure((void*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__3), 8, 4);
lean_closure_set(v___f_147_, 0, v_inst_143_);
lean_closure_set(v___f_147_, 1, v_inst_144_);
lean_closure_set(v___f_147_, 2, v_inst_145_);
lean_closure_set(v___f_147_, 3, v___f_146_);
return v___f_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(lean_object* v_m_148_, lean_object* v_00_u03b1_149_, lean_object* v_00_u03b3_150_, lean_object* v_00_u03b2_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_inst_154_, lean_object* v_inst_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg(v_inst_152_, v_inst_153_, v_inst_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___boxed(lean_object* v_m_157_, lean_object* v_00_u03b1_158_, lean_object* v_00_u03b3_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId(v_m_157_, v_00_u03b1_158_, v_00_u03b3_159_, v_00_u03b2_160_, v_inst_161_, v_inst_162_, v_inst_163_, v_inst_164_);
lean_dec(v_inst_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg___lam__1(lean_object* v_a_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v_a_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg___lam__2(lean_object* v_toFunctor_168_, lean_object* v_f_169_, lean_object* v___f_170_, lean_object* v_toBind_171_, lean_object* v___f_172_, lean_object* v_x1_173_, lean_object* v_x2_174_, lean_object* v_x3_175_){
_start:
{
lean_object* v_map_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_map_176_ = lean_ctor_get(v_toFunctor_168_, 0);
lean_inc(v_map_176_);
lean_dec_ref(v_toFunctor_168_);
v___x_177_ = lean_apply_2(v_f_169_, v_x3_175_, v_x1_173_);
v___x_178_ = lean_apply_4(v_map_176_, lean_box(0), lean_box(0), v___f_170_, v___x_177_);
v___x_179_ = lean_apply_4(v_toBind_171_, lean_box(0), lean_box(0), v___x_178_, v___f_172_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___redArg(lean_object* v_inst_181_, lean_object* v_f_182_, lean_object* v_init_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_s_186_){
_start:
{
lean_object* v_toApplicative_187_; lean_object* v_toBind_188_; lean_object* v_toFunctor_189_; lean_object* v_toPure_190_; lean_object* v___f_191_; lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_196_; 
v_toApplicative_187_ = lean_ctor_get(v_inst_181_, 0);
lean_inc_ref(v_toApplicative_187_);
v_toBind_188_ = lean_ctor_get(v_inst_181_, 1);
lean_inc(v_toBind_188_);
lean_dec_ref(v_inst_181_);
v_toFunctor_189_ = lean_ctor_get(v_toApplicative_187_, 0);
lean_inc_ref(v_toFunctor_189_);
v_toPure_190_ = lean_ctor_get(v_toApplicative_187_, 1);
lean_inc(v_toPure_190_);
lean_dec_ref(v_toApplicative_187_);
v___f_191_ = ((lean_object*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0));
v___f_192_ = ((lean_object*)(l_Std_Slice_foldlM___redArg___closed__0));
v___x_193_ = lean_apply_1(v_inst_184_, v_s_186_);
v___f_194_ = lean_alloc_closure((void*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1), 2, 1);
lean_closure_set(v___f_194_, 0, v_toPure_190_);
v___f_195_ = lean_alloc_closure((void*)(l_Std_Slice_foldlM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_195_, 0, v_toFunctor_189_);
lean_closure_set(v___f_195_, 1, v_f_182_);
lean_closure_set(v___f_195_, 2, v___f_192_);
lean_closure_set(v___f_195_, 3, v_toBind_188_);
lean_closure_set(v___f_195_, 4, v___f_194_);
v___x_196_ = lean_apply_6(v_inst_185_, v___f_191_, lean_box(0), lean_box(0), v___x_193_, v_init_183_, v___f_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldlM(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b3_198_, lean_object* v_00_u03b2_199_, lean_object* v_00_u03b4_200_, lean_object* v_m_201_, lean_object* v_inst_202_, lean_object* v_f_203_, lean_object* v_init_204_, lean_object* v_inst_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_s_208_){
_start:
{
lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v_toFunctor_211_; lean_object* v_toPure_212_; lean_object* v___f_213_; lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___f_216_; lean_object* v___f_217_; lean_object* v___x_218_; 
v_toApplicative_209_ = lean_ctor_get(v_inst_202_, 0);
lean_inc_ref(v_toApplicative_209_);
v_toBind_210_ = lean_ctor_get(v_inst_202_, 1);
lean_inc(v_toBind_210_);
lean_dec_ref(v_inst_202_);
v_toFunctor_211_ = lean_ctor_get(v_toApplicative_209_, 0);
lean_inc_ref(v_toFunctor_211_);
v_toPure_212_ = lean_ctor_get(v_toApplicative_209_, 1);
lean_inc(v_toPure_212_);
lean_dec_ref(v_toApplicative_209_);
v___f_213_ = ((lean_object*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0));
v___f_214_ = ((lean_object*)(l_Std_Slice_foldlM___redArg___closed__0));
v___x_215_ = lean_apply_1(v_inst_205_, v_s_208_);
v___f_216_ = lean_alloc_closure((void*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___lam__1), 2, 1);
lean_closure_set(v___f_216_, 0, v_toPure_212_);
v___f_217_ = lean_alloc_closure((void*)(l_Std_Slice_foldlM___redArg___lam__2), 8, 5);
lean_closure_set(v___f_217_, 0, v_toFunctor_211_);
lean_closure_set(v___f_217_, 1, v_f_203_);
lean_closure_set(v___f_217_, 2, v___f_214_);
lean_closure_set(v___f_217_, 3, v_toBind_210_);
lean_closure_set(v___f_217_, 4, v___f_216_);
v___x_218_ = lean_apply_6(v_inst_207_, v___f_213_, lean_box(0), lean_box(0), v___x_215_, v_init_204_, v___f_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldlM___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b3_220_, lean_object* v_00_u03b2_221_, lean_object* v_00_u03b4_222_, lean_object* v_m_223_, lean_object* v_inst_224_, lean_object* v_f_225_, lean_object* v_init_226_, lean_object* v_inst_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_s_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_Slice_foldlM(v_00_u03b1_219_, v_00_u03b3_220_, v_00_u03b2_221_, v_00_u03b4_222_, v_m_223_, v_inst_224_, v_f_225_, v_init_226_, v_inst_227_, v_inst_228_, v_inst_229_, v_s_230_);
lean_dec(v_inst_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldl___redArg___lam__1(lean_object* v_f_232_, lean_object* v_x1_233_, lean_object* v_x2_234_, lean_object* v_x3_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_apply_2(v_f_232_, v_x3_235_, v_x1_233_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldl___redArg(lean_object* v_f_238_, lean_object* v_init_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_s_242_){
_start:
{
lean_object* v___f_243_; lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___f_243_ = ((lean_object*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0));
v___f_244_ = lean_alloc_closure((void*)(l_Std_Slice_foldl___redArg___lam__1), 4, 1);
lean_closure_set(v___f_244_, 0, v_f_238_);
v___x_245_ = lean_apply_1(v_inst_240_, v_s_242_);
v___x_246_ = lean_apply_6(v_inst_241_, v___f_243_, lean_box(0), lean_box(0), v___x_245_, v_init_239_, v___f_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldl(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b3_248_, lean_object* v_00_u03b2_249_, lean_object* v_00_u03b4_250_, lean_object* v_f_251_, lean_object* v_init_252_, lean_object* v_inst_253_, lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_s_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___f_257_ = ((lean_object*)(l_Std_Slice_instForInOfMonadOfToIteratorOfIteratorLoopId___redArg___closed__0));
v___f_258_ = lean_alloc_closure((void*)(l_Std_Slice_foldl___redArg___lam__1), 4, 1);
lean_closure_set(v___f_258_, 0, v_f_251_);
v___x_259_ = lean_apply_1(v_inst_253_, v_s_256_);
v___x_260_ = lean_apply_6(v_inst_255_, v___f_257_, lean_box(0), lean_box(0), v___x_259_, v_init_252_, v___f_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_foldl___boxed(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b3_262_, lean_object* v_00_u03b2_263_, lean_object* v_00_u03b4_264_, lean_object* v_f_265_, lean_object* v_init_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_s_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Slice_foldl(v_00_u03b1_261_, v_00_u03b3_262_, v_00_u03b2_263_, v_00_u03b4_264_, v_f_265_, v_init_266_, v_inst_267_, v_inst_268_, v_inst_269_, v_s_270_);
lean_dec(v_inst_268_);
return v_res_271_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_ToIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Slice_Operations(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_ToIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_ToIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Slice_Operations(builtin);
}
#ifdef __cplusplus
}
#endif
