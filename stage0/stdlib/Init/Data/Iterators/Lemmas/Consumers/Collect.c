// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Collect
// Imports: public import Init.Data.Iterators.Consumers.Access import all Init.Data.Iterators.Consumers.Access import all Init.Data.Iterators.Consumers.Collect import all Init.Data.Iterators.Consumers.Total import all Init.Data.Iterators.Consumers.Monadic.Total public import Init.Data.Iterators.Consumers.Collect import Init.Data.Array.Bootstrap import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v_it_5_; lean_object* v_out_6_; lean_object* v___x_7_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__2_3_);
v_it_5_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_5_);
v_out_6_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_out_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_2(v_h__1_2_, v_it_5_, v_out_6_);
return v___x_7_;
}
case 1:
{
lean_object* v_it_8_; lean_object* v___x_9_; 
lean_dec(v_h__3_4_);
lean_dec(v_h__1_2_);
v_it_8_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_it_8_);
lean_dec_ref(v_x_1_);
v___x_9_ = lean_apply_1(v_h__2_3_, v_it_8_);
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; lean_object* v___x_11_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_box(0);
v___x_11_ = lean_apply_1(v_h__3_4_, v___x_10_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v_it_19_; lean_object* v_out_20_; lean_object* v___x_21_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__2_17_);
v_it_19_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_it_19_);
v_out_20_ = lean_ctor_get(v_x_15_, 1);
lean_inc(v_out_20_);
lean_dec_ref(v_x_15_);
v___x_21_ = lean_apply_2(v_h__1_16_, v_it_19_, v_out_20_);
return v___x_21_;
}
case 1:
{
lean_object* v_it_22_; lean_object* v___x_23_; 
lean_dec(v_h__3_18_);
lean_dec(v_h__1_16_);
v_it_22_ = lean_ctor_get(v_x_15_, 0);
lean_inc(v_it_22_);
lean_dec_ref(v_x_15_);
v___x_23_ = lean_apply_1(v_h__2_17_, v_it_22_);
return v___x_23_;
}
default: 
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_17_);
lean_dec(v_h__1_16_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__3_18_, v___x_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(lean_object* v_x_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_, lean_object* v_h__3_29_){
_start:
{
switch(lean_obj_tag(v_x_26_))
{
case 0:
{
lean_object* v_it_30_; lean_object* v_out_31_; lean_object* v___x_32_; 
lean_dec(v_h__3_29_);
lean_dec(v_h__2_28_);
v_it_30_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_it_30_);
v_out_31_ = lean_ctor_get(v_x_26_, 1);
lean_inc(v_out_31_);
lean_dec_ref(v_x_26_);
v___x_32_ = lean_apply_3(v_h__1_27_, v_it_30_, v_out_31_, lean_box(0));
return v___x_32_;
}
case 1:
{
lean_object* v_it_33_; lean_object* v___x_34_; 
lean_dec(v_h__3_29_);
lean_dec(v_h__1_27_);
v_it_33_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_it_33_);
lean_dec_ref(v_x_26_);
v___x_34_ = lean_apply_2(v_h__2_28_, v_it_33_, lean_box(0));
return v___x_34_;
}
default: 
{
lean_object* v___x_35_; 
lean_dec(v_h__2_28_);
lean_dec(v_h__1_27_);
v___x_35_ = lean_apply_1(v_h__3_29_, lean_box(0));
return v___x_35_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_inst_38_, lean_object* v_it_39_, lean_object* v_motive_40_, lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_, lean_object* v_h__3_44_){
_start:
{
switch(lean_obj_tag(v_x_41_))
{
case 0:
{
lean_object* v_it_45_; lean_object* v_out_46_; lean_object* v___x_47_; 
lean_dec(v_h__3_44_);
lean_dec(v_h__2_43_);
v_it_45_ = lean_ctor_get(v_x_41_, 0);
lean_inc(v_it_45_);
v_out_46_ = lean_ctor_get(v_x_41_, 1);
lean_inc(v_out_46_);
lean_dec_ref(v_x_41_);
v___x_47_ = lean_apply_3(v_h__1_42_, v_it_45_, v_out_46_, lean_box(0));
return v___x_47_;
}
case 1:
{
lean_object* v_it_48_; lean_object* v___x_49_; 
lean_dec(v_h__3_44_);
lean_dec(v_h__1_42_);
v_it_48_ = lean_ctor_get(v_x_41_, 0);
lean_inc(v_it_48_);
lean_dec_ref(v_x_41_);
v___x_49_ = lean_apply_2(v_h__2_43_, v_it_48_, lean_box(0));
return v___x_49_;
}
default: 
{
lean_object* v___x_50_; 
lean_dec(v_h__2_43_);
lean_dec(v_h__1_42_);
v___x_50_ = lean_apply_1(v_h__3_44_, lean_box(0));
return v___x_50_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(lean_object* v_00_u03b1_51_, lean_object* v_00_u03b2_52_, lean_object* v_inst_53_, lean_object* v_it_54_, lean_object* v_motive_55_, lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_51_, v_00_u03b2_52_, v_inst_53_, v_it_54_, v_motive_55_, v_x_56_, v_h__1_57_, v_h__2_58_, v_h__3_59_);
lean_dec(v_it_54_);
lean_dec(v_inst_53_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(lean_object* v_n_61_, lean_object* v_recur_62_, lean_object* v_h__1_63_, lean_object* v_h__2_64_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_n_61_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_object* v___x_67_; 
lean_dec(v_h__2_64_);
v___x_67_ = lean_apply_1(v_h__1_63_, v_recur_62_);
return v___x_67_;
}
else
{
lean_object* v_one_68_; lean_object* v_n_69_; lean_object* v___x_70_; 
lean_dec(v_h__1_63_);
v_one_68_ = lean_unsigned_to_nat(1u);
v_n_69_ = lean_nat_sub(v_n_61_, v_one_68_);
v___x_70_ = lean_apply_2(v_h__2_64_, v_n_69_, v_recur_62_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(lean_object* v_n_71_, lean_object* v_recur_72_, lean_object* v_h__1_73_, lean_object* v_h__2_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_71_, v_recur_72_, v_h__1_73_, v_h__2_74_);
lean_dec(v_n_71_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_it_79_, lean_object* v_motive_80_, lean_object* v_n_81_, lean_object* v_recur_82_, lean_object* v_h__1_83_, lean_object* v_h__2_84_){
_start:
{
lean_object* v_zero_85_; uint8_t v_isZero_86_; 
v_zero_85_ = lean_unsigned_to_nat(0u);
v_isZero_86_ = lean_nat_dec_eq(v_n_81_, v_zero_85_);
if (v_isZero_86_ == 1)
{
lean_object* v___x_87_; 
lean_dec(v_h__2_84_);
v___x_87_ = lean_apply_1(v_h__1_83_, v_recur_82_);
return v___x_87_;
}
else
{
lean_object* v_one_88_; lean_object* v_n_89_; lean_object* v___x_90_; 
lean_dec(v_h__1_83_);
v_one_88_ = lean_unsigned_to_nat(1u);
v_n_89_ = lean_nat_sub(v_n_81_, v_one_88_);
v___x_90_ = lean_apply_2(v_h__2_84_, v_n_89_, v_recur_82_);
return v___x_90_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_inst_93_, lean_object* v_it_94_, lean_object* v_motive_95_, lean_object* v_n_96_, lean_object* v_recur_97_, lean_object* v_h__1_98_, lean_object* v_h__2_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Collect_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_91_, v_00_u03b2_92_, v_inst_93_, v_it_94_, v_motive_95_, v_n_96_, v_recur_97_, v_h__1_98_, v_h__2_99_);
lean_dec(v_n_96_);
lean_dec(v_it_94_);
lean_dec(v_inst_93_);
return v_res_100_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Total(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Total(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
}
#ifdef __cplusplus
}
#endif
