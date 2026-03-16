// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Drop
// Imports: public import Std.Data.Iterators.Combinators.Drop public import Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop public import Init.Data.Iterators.Lemmas.Combinators.Take import Init.Data.Array.Lemmas import Init.Data.Iterators.Lemmas.Basic import Init.Data.Iterators.Lemmas.Consumers.Access import Init.Data.Iterators.Lemmas.Consumers.Collect import Init.Data.List.Nat.TakeDrop import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_, lean_object* v_h__3_4_){
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
v___x_7_ = lean_apply_3(v_h__1_2_, v_it_5_, v_out_6_, lean_box(0));
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
v___x_9_ = lean_apply_2(v_h__2_3_, v_it_8_, lean_box(0));
return v___x_9_;
}
default: 
{
lean_object* v___x_10_; 
lean_dec(v_h__2_3_);
lean_dec(v_h__1_2_);
v___x_10_ = lean_apply_1(v_h__3_4_, lean_box(0));
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(lean_object* v_00_u03b1_11_, lean_object* v_m_12_, lean_object* v_00_u03b2_13_, lean_object* v_inst_14_, lean_object* v_it_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_, lean_object* v_h__3_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___redArg(v_x_17_, v_h__1_18_, v_h__2_19_, v_h__3_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter___boxed(lean_object* v_00_u03b1_22_, lean_object* v_m_23_, lean_object* v_00_u03b2_24_, lean_object* v_inst_25_, lean_object* v_it_26_, lean_object* v_motive_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_, lean_object* v_h__3_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__3_splitter(v_00_u03b1_22_, v_m_23_, v_00_u03b2_24_, v_inst_25_, v_it_26_, v_motive_27_, v_x_28_, v_h__1_29_, v_h__2_30_, v_h__3_31_);
lean_dec(v_it_26_);
lean_dec(v_inst_25_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(lean_object* v_n_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v_zero_36_; uint8_t v_isZero_37_; 
v_zero_36_ = lean_unsigned_to_nat(0u);
v_isZero_37_ = lean_nat_dec_eq(v_n_33_, v_zero_36_);
if (v_isZero_37_ == 1)
{
lean_object* v___x_38_; 
lean_dec(v_h__2_35_);
v___x_38_ = lean_apply_1(v_h__1_34_, lean_box(0));
return v___x_38_;
}
else
{
lean_object* v_one_39_; lean_object* v_n_40_; lean_object* v___x_41_; 
lean_dec(v_h__1_34_);
v_one_39_ = lean_unsigned_to_nat(1u);
v_n_40_ = lean_nat_sub(v_n_33_, v_one_39_);
v___x_41_ = lean_apply_2(v_h__2_35_, v_n_40_, lean_box(0));
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg___boxed(lean_object* v_n_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(v_n_42_, v_h__1_43_, v_h__2_44_);
lean_dec(v_n_42_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(lean_object* v_motive_46_, lean_object* v_n_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___redArg(v_n_47_, v_h__1_48_, v_h__2_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter___boxed(lean_object* v_motive_51_, lean_object* v_n_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_IterM_step__drop_match__1_splitter(v_motive_51_, v_n_52_, v_h__1_53_, v_h__2_54_);
lean_dec(v_n_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(lean_object* v_x_56_, lean_object* v_h__1_57_, lean_object* v_h__2_58_, lean_object* v_h__3_59_){
_start:
{
switch(lean_obj_tag(v_x_56_))
{
case 0:
{
lean_object* v_it_60_; lean_object* v_out_61_; lean_object* v___x_62_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__2_58_);
v_it_60_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_it_60_);
v_out_61_ = lean_ctor_get(v_x_56_, 1);
lean_inc(v_out_61_);
lean_dec_ref(v_x_56_);
v___x_62_ = lean_apply_3(v_h__1_57_, v_it_60_, v_out_61_, lean_box(0));
return v___x_62_;
}
case 1:
{
lean_object* v_it_63_; lean_object* v___x_64_; 
lean_dec(v_h__3_59_);
lean_dec(v_h__1_57_);
v_it_63_ = lean_ctor_get(v_x_56_, 0);
lean_inc(v_it_63_);
lean_dec_ref(v_x_56_);
v___x_64_ = lean_apply_2(v_h__2_58_, v_it_63_, lean_box(0));
return v___x_64_;
}
default: 
{
lean_object* v___x_65_; 
lean_dec(v_h__2_58_);
lean_dec(v_h__1_57_);
v___x_65_ = lean_apply_1(v_h__3_59_, lean_box(0));
return v___x_65_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_it_69_, lean_object* v_motive_70_, lean_object* v_x_71_, lean_object* v_h__1_72_, lean_object* v_h__2_73_, lean_object* v_h__3_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___redArg(v_x_71_, v_h__1_72_, v_h__2_73_, v_h__3_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter___boxed(lean_object* v_00_u03b1_76_, lean_object* v_00_u03b2_77_, lean_object* v_inst_78_, lean_object* v_it_79_, lean_object* v_motive_80_, lean_object* v_x_81_, lean_object* v_h__1_82_, lean_object* v_h__2_83_, lean_object* v_h__3_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__3_splitter(v_00_u03b1_76_, v_00_u03b2_77_, v_inst_78_, v_it_79_, v_motive_80_, v_x_81_, v_h__1_82_, v_h__2_83_, v_h__3_84_);
lean_dec(v_it_79_);
lean_dec(v_inst_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(lean_object* v_n_86_, lean_object* v_h__1_87_, lean_object* v_h__2_88_){
_start:
{
lean_object* v_zero_89_; uint8_t v_isZero_90_; 
v_zero_89_ = lean_unsigned_to_nat(0u);
v_isZero_90_ = lean_nat_dec_eq(v_n_86_, v_zero_89_);
if (v_isZero_90_ == 1)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_h__2_88_);
v___x_91_ = lean_box(0);
v___x_92_ = lean_apply_1(v_h__1_87_, v___x_91_);
return v___x_92_;
}
else
{
lean_object* v_one_93_; lean_object* v_n_94_; lean_object* v___x_95_; 
lean_dec(v_h__1_87_);
v_one_93_ = lean_unsigned_to_nat(1u);
v_n_94_ = lean_nat_sub(v_n_86_, v_one_93_);
v___x_95_ = lean_apply_1(v_h__2_88_, v_n_94_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg___boxed(lean_object* v_n_96_, lean_object* v_h__1_97_, lean_object* v_h__2_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(v_n_96_, v_h__1_97_, v_h__2_98_);
lean_dec(v_n_96_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(lean_object* v_motive_100_, lean_object* v_n_101_, lean_object* v_h__1_102_, lean_object* v_h__2_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___redArg(v_n_101_, v_h__1_102_, v_h__2_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter___boxed(lean_object* v_motive_105_, lean_object* v_n_106_, lean_object* v_h__1_107_, lean_object* v_h__2_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Std_Data_Iterators_Lemmas_Combinators_Drop_0__Std_Iter_step__drop_match__1_splitter(v_motive_105_, v_n_106_, v_h__1_107_, v_h__2_108_);
lean_dec(v_n_106_);
return v_res_109_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Drop(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Drop(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
}
#ifdef __cplusplus
}
#endif
