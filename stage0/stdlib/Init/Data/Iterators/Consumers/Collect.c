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
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_val_5_, 2);
v___x_8_ = lean_array_push(v_acc_3_, v_out_7_);
v___x_9_ = lean_apply_3(v_recur_4_, v_it_6_, v___x_8_, lean_box(0));
return v___x_9_;
}
case 1:
{
lean_object* v_it_10_; lean_object* v___x_11_; 
v_it_10_ = lean_ctor_get(v_val_5_, 0);
lean_inc(v_it_10_);
lean_dec_ref_known(v_val_5_, 1);
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
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray___redArg(lean_object* v_inst_26_, lean_object* v_it_27_){
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
LEAN_EXPORT lean_object* l_Std_Iter_Total_toArray(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_it_35_){
_start:
{
lean_object* v___f_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___f_36_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_36_, 0, v_inst_33_);
v___x_37_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_38_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_36_, v_it_35_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg___lam__0(lean_object* v_inst_39_, lean_object* v_it_40_, lean_object* v_acc_41_, lean_object* v_recur_42_){
_start:
{
lean_object* v_val_43_; 
v_val_43_ = lean_apply_1(v_inst_39_, v_it_40_);
switch(lean_obj_tag(v_val_43_))
{
case 0:
{
lean_object* v_it_44_; lean_object* v_out_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
v_it_44_ = lean_ctor_get(v_val_43_, 0);
v_out_45_ = lean_ctor_get(v_val_43_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_val_43_);
if (v_isSharedCheck_53_ == 0)
{
v___x_47_ = v_val_43_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_out_45_);
lean_inc(v_it_44_);
lean_dec(v_val_43_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 1);
lean_ctor_set(v___x_47_, 1, v_acc_41_);
lean_ctor_set(v___x_47_, 0, v_out_45_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_out_45_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v_acc_41_);
v___x_50_ = v_reuseFailAlloc_52_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_3(v_recur_42_, v_it_44_, v___x_50_, lean_box(0));
return v___x_51_;
}
}
}
case 1:
{
lean_object* v_it_54_; lean_object* v___x_55_; 
v_it_54_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_it_54_);
lean_dec_ref_known(v_val_43_, 1);
v___x_55_ = lean_apply_3(v_recur_42_, v_it_54_, v_acc_41_, lean_box(0));
return v___x_55_;
}
default: 
{
lean_dec_ref(v_recur_42_);
return v_acc_41_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev___redArg(lean_object* v_inst_56_, lean_object* v_it_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___f_58_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_58_, 0, v_inst_56_);
v___x_59_ = lean_box(0);
v___x_60_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_58_, v_it_57_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toListRev(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_inst_63_, lean_object* v_it_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___f_65_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_65_, 0, v_inst_63_);
v___x_66_ = lean_box(0);
v___x_67_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_65_, v_it_64_, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev___redArg(lean_object* v_inst_68_, lean_object* v_it_69_){
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
LEAN_EXPORT lean_object* l_Std_Iter_Total_toListRev(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_it_77_){
_start:
{
lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___f_78_ = lean_alloc_closure((void*)(l_Std_Iter_toListRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_78_, 0, v_inst_75_);
v___x_79_ = lean_box(0);
v___x_80_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_78_, v_it_77_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList___redArg(lean_object* v_inst_81_, lean_object* v_it_82_){
_start:
{
lean_object* v___f_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___f_83_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_83_, 0, v_inst_81_);
v___x_84_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_85_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_83_, v_it_82_, v___x_84_);
v___x_86_ = lean_array_to_list(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toList(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_inst_89_, lean_object* v_it_90_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___f_91_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_91_, 0, v_inst_89_);
v___x_92_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_93_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_91_, v_it_90_, v___x_92_);
v___x_94_ = lean_array_to_list(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList___redArg(lean_object* v_inst_95_, lean_object* v_it_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___f_97_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_97_, 0, v_inst_95_);
v___x_98_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_99_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_97_, v_it_96_, v___x_98_);
v___x_100_ = lean_array_to_list(v___x_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_toList(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_it_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___f_106_ = lean_alloc_closure((void*)(l_Std_Iter_toArray___redArg___lam__0), 4, 1);
lean_closure_set(v___f_106_, 0, v_inst_103_);
v___x_107_ = ((lean_object*)(l_Std_Iter_toArray___redArg___closed__0));
v___x_108_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_106_, v_it_105_, v___x_107_);
v___x_109_ = lean_array_to_list(v___x_108_);
return v___x_109_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
