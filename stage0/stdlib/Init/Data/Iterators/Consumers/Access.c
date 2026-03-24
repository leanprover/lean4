// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Access
// Imports: public import Init.Data.Iterators.Consumers.Monadic.Access public import Init.Data.Iterators.Consumers.Partial public import Init.Data.Iterators.Consumers.Total public import Init.Ext public import Init.WFExtrinsicFix
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
lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_it_2_, lean_object* v_n_3_, lean_object* v_recur_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_1(v_inst_1_, v_it_2_);
switch(lean_obj_tag(v___x_5_))
{
case 0:
{
lean_object* v_it_6_; lean_object* v_out_7_; lean_object* v_zero_8_; uint8_t v_isZero_9_; 
v_it_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_it_6_);
v_out_7_ = lean_ctor_get(v___x_5_, 1);
lean_inc(v_out_7_);
lean_dec_ref(v___x_5_);
v_zero_8_ = lean_unsigned_to_nat(0u);
v_isZero_9_ = lean_nat_dec_eq(v_n_3_, v_zero_8_);
if (v_isZero_9_ == 1)
{
lean_object* v___x_10_; 
lean_dec(v_it_6_);
lean_dec_ref(v_recur_4_);
lean_dec(v_n_3_);
v___x_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_10_, 0, v_out_7_);
return v___x_10_;
}
else
{
lean_object* v_one_11_; lean_object* v_n_12_; lean_object* v___x_13_; 
lean_dec(v_out_7_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_n_12_ = lean_nat_sub(v_n_3_, v_one_11_);
lean_dec(v_n_3_);
v___x_13_ = lean_apply_3(v_recur_4_, v_it_6_, v_n_12_, lean_box(0));
return v___x_13_;
}
}
case 1:
{
lean_object* v_it_14_; lean_object* v___x_15_; 
v_it_14_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_it_14_);
lean_dec_ref(v___x_5_);
v___x_15_ = lean_apply_3(v_recur_4_, v_it_14_, v_n_3_, lean_box(0));
return v___x_15_;
}
default: 
{
lean_object* v___x_16_; 
lean_dec_ref(v_recur_4_);
lean_dec(v_n_3_);
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f___redArg(lean_object* v_inst_17_, lean_object* v_n_18_, lean_object* v_it_19_){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; 
v___f_20_ = lean_alloc_closure((void*)(l_Std_Iter_atIdxSlow_x3f___redArg___lam__0), 4, 1);
lean_closure_set(v___f_20_, 0, v_inst_17_);
v___x_21_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(v___f_20_, v_it_19_, v_n_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdxSlow_x3f(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_n_25_, lean_object* v_it_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_24_, v_n_25_, v_it_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
switch(lean_obj_tag(v_x_28_))
{
case 0:
{
lean_object* v_it_32_; lean_object* v_out_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_31_);
lean_dec(v_h__2_30_);
v_it_32_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_it_32_);
v_out_33_ = lean_ctor_get(v_x_28_, 1);
lean_inc(v_out_33_);
lean_dec_ref(v_x_28_);
v___x_34_ = lean_apply_3(v_h__1_29_, v_it_32_, v_out_33_, lean_box(0));
return v___x_34_;
}
case 1:
{
lean_object* v_it_35_; lean_object* v___x_36_; 
lean_dec(v_h__3_31_);
lean_dec(v_h__1_29_);
v_it_35_ = lean_ctor_get(v_x_28_, 0);
lean_inc(v_it_35_);
lean_dec_ref(v_x_28_);
v___x_36_ = lean_apply_2(v_h__2_30_, v_it_35_, lean_box(0));
return v___x_36_;
}
default: 
{
lean_object* v___x_37_; 
lean_dec(v_h__2_30_);
lean_dec(v_h__1_29_);
v___x_37_ = lean_apply_1(v_h__3_31_, lean_box(0));
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_inst_40_, lean_object* v_it_41_, lean_object* v_motive_42_, lean_object* v_x_43_, lean_object* v_h__1_44_, lean_object* v_h__2_45_, lean_object* v_h__3_46_){
_start:
{
switch(lean_obj_tag(v_x_43_))
{
case 0:
{
lean_object* v_it_47_; lean_object* v_out_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__2_45_);
v_it_47_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_it_47_);
v_out_48_ = lean_ctor_get(v_x_43_, 1);
lean_inc(v_out_48_);
lean_dec_ref(v_x_43_);
v___x_49_ = lean_apply_3(v_h__1_44_, v_it_47_, v_out_48_, lean_box(0));
return v___x_49_;
}
case 1:
{
lean_object* v_it_50_; lean_object* v___x_51_; 
lean_dec(v_h__3_46_);
lean_dec(v_h__1_44_);
v_it_50_ = lean_ctor_get(v_x_43_, 0);
lean_inc(v_it_50_);
lean_dec_ref(v_x_43_);
v___x_51_ = lean_apply_2(v_h__2_45_, v_it_50_, lean_box(0));
return v___x_51_;
}
default: 
{
lean_object* v___x_52_; 
lean_dec(v_h__2_45_);
lean_dec(v_h__1_44_);
v___x_52_ = lean_apply_1(v_h__3_46_, lean_box(0));
return v___x_52_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* v_00_u03b1_53_, lean_object* v_00_u03b2_54_, lean_object* v_inst_55_, lean_object* v_it_56_, lean_object* v_motive_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_, lean_object* v_h__3_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_53_, v_00_u03b2_54_, v_inst_55_, v_it_56_, v_motive_57_, v_x_58_, v_h__1_59_, v_h__2_60_, v_h__3_61_);
lean_dec(v_it_56_);
lean_dec(v_inst_55_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object* v_n_63_, lean_object* v_recur_64_, lean_object* v_h__1_65_, lean_object* v_h__2_66_){
_start:
{
lean_object* v_zero_67_; uint8_t v_isZero_68_; 
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_n_63_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_69_; 
lean_dec(v_h__2_66_);
v___x_69_ = lean_apply_1(v_h__1_65_, v_recur_64_);
return v___x_69_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; lean_object* v___x_72_; 
lean_dec(v_h__1_65_);
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_n_63_, v_one_70_);
v___x_72_ = lean_apply_2(v_h__2_66_, v_n_71_, v_recur_64_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object* v_n_73_, lean_object* v_recur_74_, lean_object* v_h__1_75_, lean_object* v_h__2_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_73_, v_recur_74_, v_h__1_75_, v_h__2_76_);
lean_dec(v_n_73_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_inst_80_, lean_object* v_it_81_, lean_object* v_motive_82_, lean_object* v_n_83_, lean_object* v_recur_84_, lean_object* v_h__1_85_, lean_object* v_h__2_86_){
_start:
{
lean_object* v_zero_87_; uint8_t v_isZero_88_; 
v_zero_87_ = lean_unsigned_to_nat(0u);
v_isZero_88_ = lean_nat_dec_eq(v_n_83_, v_zero_87_);
if (v_isZero_88_ == 1)
{
lean_object* v___x_89_; 
lean_dec(v_h__2_86_);
v___x_89_ = lean_apply_1(v_h__1_85_, v_recur_84_);
return v___x_89_;
}
else
{
lean_object* v_one_90_; lean_object* v_n_91_; lean_object* v___x_92_; 
lean_dec(v_h__1_85_);
v_one_90_ = lean_unsigned_to_nat(1u);
v_n_91_ = lean_nat_sub(v_n_83_, v_one_90_);
v___x_92_ = lean_apply_2(v_h__2_86_, v_n_91_, v_recur_84_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_93_, lean_object* v_00_u03b2_94_, lean_object* v_inst_95_, lean_object* v_it_96_, lean_object* v_motive_97_, lean_object* v_n_98_, lean_object* v_recur_99_, lean_object* v_h__1_100_, lean_object* v_h__2_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_93_, v_00_u03b2_94_, v_inst_95_, v_it_96_, v_motive_97_, v_n_98_, v_recur_99_, v_h__1_100_, v_h__2_101_);
lean_dec(v_n_98_);
lean_dec(v_it_96_);
lean_dec(v_inst_95_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f___redArg(lean_object* v_inst_103_, lean_object* v_n_104_, lean_object* v_it_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_103_, v_n_104_, v_it_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_n_111_, lean_object* v_it_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_109_, v_n_111_, v_it_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f___redArg(lean_object* v_inst_114_, lean_object* v_n_115_, lean_object* v_it_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_114_, v_n_115_, v_it_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_inst_120_, lean_object* v_n_121_, lean_object* v_it_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_120_, v_n_121_, v_it_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___redArg(lean_object* v_inst_124_, lean_object* v_n_125_, lean_object* v_it_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_apply_2(v_inst_124_, v_it_126_, v_n_125_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_out_128_; lean_object* v___x_129_; 
v_out_128_ = lean_ctor_get(v___x_127_, 1);
lean_inc(v_out_128_);
lean_dec_ref(v___x_127_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_out_128_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; 
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_n_135_, lean_object* v_it_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_2(v_inst_134_, v_it_136_, v_n_135_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_out_138_; lean_object* v___x_139_; 
v_out_138_ = lean_ctor_get(v___x_137_, 1);
lean_inc(v_out_138_);
lean_dec_ref(v___x_137_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_out_138_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; 
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_n_145_, lean_object* v_it_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Iter_atIdx_x3f(v_00_u03b1_141_, v_00_u03b2_142_, v_inst_143_, v_inst_144_, v_n_145_, v_it_146_);
lean_dec(v_inst_143_);
return v_res_147_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_WFExtrinsicFix(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Partial(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_WFExtrinsicFix(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFExtrinsicFix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Consumers_Access(builtin);
}
#ifdef __cplusplus
}
#endif
