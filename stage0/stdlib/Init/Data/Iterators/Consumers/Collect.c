// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Collect
// Imports: public import Init.Data.Iterators.Consumers.Partial public import Init.Data.Iterators.Consumers.Total public import Init.Data.Iterators.Consumers.Monadic.Collect
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Iter_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Iter_toArray___redArg___closed__0 = (const lean_object*)&l_Std_Iter_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_it_2_, lean_object* v_acc_3_, lean_object* v_recur_4_){
_start:
{
lean_object* v_val_5_; 
v_val_5_ = lean_apply_1(v_inst_1_, v_it_2_);
switch(lean_obj_tag(v_val_5_))
{
case 0:
{
lean_object* v_it_6_; lean_object* v_out_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_it_6_ = lean_ctor_get(v_val_5_, 0);
lean_inc(v_it_6_);
v_out_7_ = lean_ctor_get(v_val_5_, 1);
lean_inc(v_out_7_);
lean_dec_ref(v_val_5_);
v___x_8_ = lean_array_push(v_acc_3_, v_out_7_);
v___x_9_ = lean_apply_3(v_recur_4_, v_it_6_, v___x_8_, lean_box(0));
return v___x_9_;
}
case 1:
{
lean_object* v_it_10_; lean_object* v___x_11_; 
v_it_10_ = lean_ctor_get(v_val_5_, 0);
lean_inc(v_it_10_);
lean_dec_ref(v_val_5_);
v___x_11_ = lean_apply_3(v_recur_4_, v_it_10_, v_acc_3_, lean_box(0));
return v___x_11_;
}
default: 
{
lean_dec_ref(v_recur_4_);
return v_acc_3_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toArray___redArg(lean_object* v_inst_14_, lean_object* v_it_15_){
_start:
{
lean_object* v___f_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___f_16_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_16_, 0, v_inst_14_);
v___x_17_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_18_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_16_, v_it_15_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toArray(lean_object* v_00_u03b1_19_, lean_object* v_00_u03b2_20_, lean_object* v_inst_21_, lean_object* v_it_22_){
_start:
{
lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_23_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_23_, 0, v_inst_21_);
v___x_24_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_25_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_23_, v_it_22_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray___redArg(lean_object* v_inst_26_, lean_object* v_it_27_){
_start:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_28_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_28_, 0, v_inst_26_);
v___x_29_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_30_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_28_, v_it_27_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toArray(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_it_34_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___f_35_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_35_, 0, v_inst_33_);
v___x_36_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_37_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_35_, v_it_34_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object* v_inst_38_, lean_object* v_it_39_){
_start:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___f_40_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_40_, 0, v_inst_38_);
v___x_41_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_42_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_40_, v_it_39_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_it_47_){
_start:
{
lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___f_48_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_48_, 0, v_inst_45_);
v___x_49_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_50_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_48_, v_it_47_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object* v_inst_51_, lean_object* v_it_52_, lean_object* v_acc_53_, lean_object* v_recur_54_){
_start:
{
lean_object* v_val_55_; 
v_val_55_ = lean_apply_1(v_inst_51_, v_it_52_);
switch(lean_obj_tag(v_val_55_))
{
case 0:
{
lean_object* v_it_56_; lean_object* v_out_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_65_; 
v_it_56_ = lean_ctor_get(v_val_55_, 0);
v_out_57_ = lean_ctor_get(v_val_55_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_val_55_);
if (v_isSharedCheck_65_ == 0)
{
v___x_59_ = v_val_55_;
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_out_57_);
lean_inc(v_it_56_);
lean_dec(v_val_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set_tag(v___x_59_, 1);
lean_ctor_set(v___x_59_, 1, v_acc_53_);
lean_ctor_set(v___x_59_, 0, v_out_57_);
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_out_57_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_acc_53_);
v___x_62_ = v_reuseFailAlloc_64_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_apply_3(v_recur_54_, v_it_56_, v___x_62_, lean_box(0));
return v___x_63_;
}
}
}
case 1:
{
lean_object* v_it_66_; lean_object* v___x_67_; 
v_it_66_ = lean_ctor_get(v_val_55_, 0);
lean_inc(v_it_66_);
lean_dec_ref(v_val_55_);
v___x_67_ = lean_apply_3(v_recur_54_, v_it_66_, v_acc_53_, lean_box(0));
return v___x_67_;
}
default: 
{
lean_dec_ref(v_recur_54_);
return v_acc_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object* v_inst_68_, lean_object* v_it_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___f_70_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_70_, 0, v_inst_68_);
v___x_71_ = lean_box(0);
v___x_72_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_70_, v_it_69_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_inst_75_, lean_object* v_it_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___f_77_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_77_, 0, v_inst_75_);
v___x_78_ = lean_box(0);
v___x_79_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_77_, v_it_76_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev___redArg(lean_object* v_inst_80_, lean_object* v_it_81_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___f_82_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_82_, 0, v_inst_80_);
v___x_83_ = lean_box(0);
v___x_84_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_82_, v_it_81_, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toListRev(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_inst_87_, lean_object* v_it_88_){
_start:
{
lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___f_89_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_89_, 0, v_inst_87_);
v___x_90_ = lean_box(0);
v___x_91_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_89_, v_it_88_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object* v_inst_92_, lean_object* v_it_93_){
_start:
{
lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___f_94_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_94_, 0, v_inst_92_);
v___x_95_ = lean_box(0);
v___x_96_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_94_, v_it_93_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_it_101_){
_start:
{
lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___f_102_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_102_, 0, v_inst_99_);
v___x_103_ = lean_box(0);
v___x_104_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_102_, v_it_101_, v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object* v_inst_105_, lean_object* v_it_106_){
_start:
{
lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___f_107_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_107_, 0, v_inst_105_);
v___x_108_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_109_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_107_, v_it_106_, v___x_108_);
v___x_110_ = lean_array_to_list(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_inst_113_, lean_object* v_it_114_){
_start:
{
lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___f_115_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_115_, 0, v_inst_113_);
v___x_116_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_117_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_115_, v_it_114_, v___x_116_);
v___x_118_ = lean_array_to_list(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList___redArg(lean_object* v_inst_119_, lean_object* v_it_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___f_121_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_121_, 0, v_inst_119_);
v___x_122_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_123_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_121_, v_it_120_, v___x_122_);
v___x_124_ = lean_array_to_list(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_toList(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_inst_127_, lean_object* v_it_128_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___f_129_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_129_, 0, v_inst_127_);
v___x_130_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_131_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_129_, v_it_128_, v___x_130_);
v___x_132_ = lean_array_to_list(v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object* v_inst_133_, lean_object* v_it_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___f_135_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_135_, 0, v_inst_133_);
v___x_136_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_137_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_135_, v_it_134_, v___x_136_);
v___x_138_ = lean_array_to_list(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_it_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___f_144_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_144_, 0, v_inst_141_);
v___x_145_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_146_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_144_, v_it_143_, v___x_145_);
v___x_147_ = lean_array_to_list(v___x_146_);
return v___x_147_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Collect(builtin);
}
#ifdef __cplusplus
}
#endif
