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
lean_object* v___x_47_; 
v___x_47_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(v_x_43_, v_h__1_44_, v_h__2_45_, v_h__3_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* v_00_u03b1_48_, lean_object* v_00_u03b2_49_, lean_object* v_inst_50_, lean_object* v_it_51_, lean_object* v_motive_52_, lean_object* v_x_53_, lean_object* v_h__1_54_, lean_object* v_h__2_55_, lean_object* v_h__3_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_48_, v_00_u03b2_49_, v_inst_50_, v_it_51_, v_motive_52_, v_x_53_, v_h__1_54_, v_h__2_55_, v_h__3_56_);
lean_dec(v_it_51_);
lean_dec(v_inst_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object* v_n_58_, lean_object* v_recur_59_, lean_object* v_h__1_60_, lean_object* v_h__2_61_){
_start:
{
lean_object* v_zero_62_; uint8_t v_isZero_63_; 
v_zero_62_ = lean_unsigned_to_nat(0u);
v_isZero_63_ = lean_nat_dec_eq(v_n_58_, v_zero_62_);
if (v_isZero_63_ == 1)
{
lean_object* v___x_64_; 
lean_dec(v_h__2_61_);
v___x_64_ = lean_apply_1(v_h__1_60_, v_recur_59_);
return v___x_64_;
}
else
{
lean_object* v_one_65_; lean_object* v_n_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_60_);
v_one_65_ = lean_unsigned_to_nat(1u);
v_n_66_ = lean_nat_sub(v_n_58_, v_one_65_);
v___x_67_ = lean_apply_2(v_h__2_61_, v_n_66_, v_recur_59_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object* v_n_68_, lean_object* v_recur_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_68_, v_recur_69_, v_h__1_70_, v_h__2_71_);
lean_dec(v_n_68_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* v_00_u03b1_73_, lean_object* v_00_u03b2_74_, lean_object* v_inst_75_, lean_object* v_it_76_, lean_object* v_motive_77_, lean_object* v_n_78_, lean_object* v_recur_79_, lean_object* v_h__1_80_, lean_object* v_h__2_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_78_, v_recur_79_, v_h__1_80_, v_h__2_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_83_, lean_object* v_00_u03b2_84_, lean_object* v_inst_85_, lean_object* v_it_86_, lean_object* v_motive_87_, lean_object* v_n_88_, lean_object* v_recur_89_, lean_object* v_h__1_90_, lean_object* v_h__2_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_83_, v_00_u03b2_84_, v_inst_85_, v_it_86_, v_motive_87_, v_n_88_, v_recur_89_, v_h__1_90_, v_h__2_91_);
lean_dec(v_n_88_);
lean_dec(v_it_86_);
lean_dec(v_inst_85_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f___redArg(lean_object* v_inst_93_, lean_object* v_n_94_, lean_object* v_it_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_93_, v_n_94_, v_it_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Total_atIdxSlow_x3f(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_n_101_, lean_object* v_it_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_99_, v_n_101_, v_it_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f___redArg(lean_object* v_inst_104_, lean_object* v_n_105_, lean_object* v_it_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_104_, v_n_105_, v_it_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Partial_atIdxSlow_x3f(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_inst_110_, lean_object* v_n_111_, lean_object* v_it_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_110_, v_n_111_, v_it_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___redArg(lean_object* v_inst_114_, lean_object* v_n_115_, lean_object* v_it_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_apply_2(v_inst_114_, v_it_116_, v_n_115_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_out_118_; lean_object* v___x_119_; 
v_out_118_ = lean_ctor_get(v___x_117_, 1);
lean_inc(v_out_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_out_118_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f(lean_object* v_00_u03b1_121_, lean_object* v_00_u03b2_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_n_125_, lean_object* v_it_126_){
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
LEAN_EXPORT lean_object* l_Std_Iter_atIdx_x3f___boxed(lean_object* v_00_u03b1_131_, lean_object* v_00_u03b2_132_, lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_n_135_, lean_object* v_it_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Iter_atIdx_x3f(v_00_u03b1_131_, v_00_u03b2_132_, v_inst_133_, v_inst_134_, v_n_135_, v_it_136_);
lean_dec(v_inst_133_);
return v_res_137_;
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
