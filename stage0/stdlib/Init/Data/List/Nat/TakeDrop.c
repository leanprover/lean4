// Lean compiler output
// Module: Init.Data.List.Nat.TakeDrop
// Imports: public import Init.Data.List.Lemmas public import Init.Data.Nat.MinMax import Init.ByCases import Init.Data.Bool import Init.Data.List.Find import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.List.Zip import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_1_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_object* v___x_8_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_8_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_8_;
}
else
{
lean_object* v_one_9_; lean_object* v_n_10_; 
lean_dec(v_h__1_3_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_n_10_ = lean_nat_sub(v_x_1_, v_one_9_);
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_11_; 
lean_dec(v_h__3_5_);
v___x_11_ = lean_apply_1(v_h__2_4_, v_n_10_);
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_4_);
v_head_12_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_12_);
v_tail_13_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_13_);
lean_dec_ref_known(v_x_2_, 2);
v___x_14_ = lean_apply_3(v_h__3_5_, v_n_10_, v_head_12_, v_tail_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___redArg___boxed(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_, lean_object* v_h__3_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___redArg(v_x_15_, v_x_16_, v_h__1_17_, v_h__2_18_, v_h__3_19_);
lean_dec(v_x_15_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter(lean_object* v_00_u03b1_21_, lean_object* v_motive_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_, lean_object* v_h__3_27_){
_start:
{
lean_object* v_zero_28_; uint8_t v_isZero_29_; 
v_zero_28_ = lean_unsigned_to_nat(0u);
v_isZero_29_ = lean_nat_dec_eq(v_x_23_, v_zero_28_);
if (v_isZero_29_ == 1)
{
lean_object* v___x_30_; 
lean_dec(v_h__3_27_);
lean_dec(v_h__2_26_);
v___x_30_ = lean_apply_1(v_h__1_25_, v_x_24_);
return v___x_30_;
}
else
{
lean_object* v_one_31_; lean_object* v_n_32_; 
lean_dec(v_h__1_25_);
v_one_31_ = lean_unsigned_to_nat(1u);
v_n_32_ = lean_nat_sub(v_x_23_, v_one_31_);
if (lean_obj_tag(v_x_24_) == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h__3_27_);
v___x_33_ = lean_apply_1(v_h__2_26_, v_n_32_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_26_);
v_head_34_ = lean_ctor_get(v_x_24_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_x_24_, 1);
lean_inc(v_tail_35_);
lean_dec_ref_known(v_x_24_, 2);
v___x_36_ = lean_apply_3(v_h__3_27_, v_n_32_, v_head_34_, v_tail_35_);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter___boxed(lean_object* v_00_u03b1_37_, lean_object* v_motive_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Init_Data_List_Nat_TakeDrop_0__List_take_match__1_splitter(v_00_u03b1_37_, v_motive_38_, v_x_39_, v_x_40_, v_h__1_41_, v_h__2_42_, v_h__3_43_);
lean_dec(v_x_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_45_, lean_object* v_h__1_46_, lean_object* v_h__2_47_){
_start:
{
if (lean_obj_tag(v_ys_45_) == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_h__2_47_);
v___x_48_ = lean_box(0);
v___x_49_ = lean_apply_1(v_h__1_46_, v___x_48_);
return v___x_49_;
}
else
{
lean_object* v_head_50_; lean_object* v_tail_51_; lean_object* v___x_52_; 
lean_dec(v_h__1_46_);
v_head_50_ = lean_ctor_get(v_ys_45_, 0);
lean_inc(v_head_50_);
v_tail_51_ = lean_ctor_get(v_ys_45_, 1);
lean_inc(v_tail_51_);
lean_dec_ref_known(v_ys_45_, 2);
v___x_52_ = lean_apply_2(v_h__2_47_, v_head_50_, v_tail_51_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_TakeDrop_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_53_, lean_object* v_motive_54_, lean_object* v_ys_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_ys_55_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_dec(v_h__2_57_);
v___x_58_ = lean_box(0);
v___x_59_ = lean_apply_1(v_h__1_56_, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v_head_60_; lean_object* v_tail_61_; lean_object* v___x_62_; 
lean_dec(v_h__1_56_);
v_head_60_ = lean_ctor_get(v_ys_55_, 0);
lean_inc(v_head_60_);
v_tail_61_ = lean_ctor_get(v_ys_55_, 1);
lean_inc(v_tail_61_);
lean_dec_ref_known(v_ys_55_, 2);
v___x_62_ = lean_apply_2(v_h__2_57_, v_head_60_, v_tail_61_);
return v___x_62_;
}
}
}
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_TakeDrop(builtin);
}
#ifdef __cplusplus
}
#endif
