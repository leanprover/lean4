// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Consumers.Access
// Imports: public import Init.Data.Iterators.Consumers.Access
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_motive_14_, lean_object* v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_, lean_object* v_h__3_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__3_splitter___redArg(v_x_15_, v_h__1_16_, v_h__2_17_, v_h__3_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(lean_object* v_n_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
lean_object* v_zero_23_; uint8_t v_isZero_24_; 
v_zero_23_ = lean_unsigned_to_nat(0u);
v_isZero_24_ = lean_nat_dec_eq(v_n_20_, v_zero_23_);
if (v_isZero_24_ == 1)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_22_);
v___x_25_ = lean_box(0);
v___x_26_ = lean_apply_1(v_h__1_21_, v___x_25_);
return v___x_26_;
}
else
{
lean_object* v_one_27_; lean_object* v_n_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_21_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_n_28_ = lean_nat_sub(v_n_20_, v_one_27_);
v___x_29_ = lean_apply_1(v_h__2_22_, v_n_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg___boxed(lean_object* v_n_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_30_, v_h__1_31_, v_h__2_32_);
lean_dec(v_n_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(lean_object* v_motive_34_, lean_object* v_n_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___redArg(v_n_35_, v_h__1_36_, v_h__2_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter___boxed(lean_object* v_motive_39_, lean_object* v_n_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Init_Data_Iterators_Lemmas_Consumers_Access_0__Std_Iter_atIdxSlow_x3f__eq__match_match__1_splitter(v_motive_39_, v_n_40_, v_h__1_41_, v_h__2_42_);
lean_dec(v_n_40_);
return v_res_43_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers_Access(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
}
#ifdef __cplusplus
}
#endif
