// Lean compiler output
// Module: Init.Data.List.Nat.InsertIdx
// Imports: public import Init.GetElem import Init.Data.List.Erase import Init.Data.List.Lemmas import Init.Data.List.Nat.Modify import Init.Data.Nat.Lemmas import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__List_eraseIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__List_eraseIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_, lean_object* v_h__3_5_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_6_; 
lean_dec(v_h__3_5_);
lean_dec(v_h__2_4_);
v___x_6_ = lean_apply_1(v_h__1_3_, v_x_2_);
return v___x_6_;
}
else
{
lean_object* v_head_7_; lean_object* v_tail_8_; lean_object* v_zero_9_; uint8_t v_isZero_10_; 
lean_dec(v_h__1_3_);
v_head_7_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_7_);
v_tail_8_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_8_);
lean_dec_ref_known(v_x_1_, 2);
v_zero_9_ = lean_unsigned_to_nat(0u);
v_isZero_10_ = lean_nat_dec_eq(v_x_2_, v_zero_9_);
if (v_isZero_10_ == 1)
{
lean_object* v___x_11_; 
lean_dec(v_h__3_5_);
lean_dec(v_x_2_);
v___x_11_ = lean_apply_2(v_h__2_4_, v_head_7_, v_tail_8_);
return v___x_11_;
}
else
{
lean_object* v_one_12_; lean_object* v_n_13_; lean_object* v___x_14_; 
lean_dec(v_h__2_4_);
v_one_12_ = lean_unsigned_to_nat(1u);
v_n_13_ = lean_nat_sub(v_x_2_, v_one_12_);
lean_dec(v_x_2_);
v___x_14_ = lean_apply_3(v_h__3_5_, v_head_7_, v_tail_8_, v_n_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_h__1_19_, lean_object* v_h__2_20_, lean_object* v_h__3_21_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_object* v___x_22_; 
lean_dec(v_h__3_21_);
lean_dec(v_h__2_20_);
v___x_22_ = lean_apply_1(v_h__1_19_, v_x_18_);
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v_tail_24_; lean_object* v_zero_25_; uint8_t v_isZero_26_; 
lean_dec(v_h__1_19_);
v_head_23_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_23_);
v_tail_24_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_tail_24_);
lean_dec_ref_known(v_x_17_, 2);
v_zero_25_ = lean_unsigned_to_nat(0u);
v_isZero_26_ = lean_nat_dec_eq(v_x_18_, v_zero_25_);
if (v_isZero_26_ == 1)
{
lean_object* v___x_27_; 
lean_dec(v_h__3_21_);
lean_dec(v_x_18_);
v___x_27_ = lean_apply_2(v_h__2_20_, v_head_23_, v_tail_24_);
return v___x_27_;
}
else
{
lean_object* v_one_28_; lean_object* v_n_29_; lean_object* v___x_30_; 
lean_dec(v_h__2_20_);
v_one_28_ = lean_unsigned_to_nat(1u);
v_n_29_ = lean_nat_sub(v_x_18_, v_one_28_);
lean_dec(v_x_18_);
v___x_30_ = lean_apply_3(v_h__3_21_, v_head_23_, v_tail_24_, v_n_29_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
if (lean_obj_tag(v_ys_31_) == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__2_33_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_32_, v___x_34_);
return v___x_35_;
}
else
{
lean_object* v_head_36_; lean_object* v_tail_37_; lean_object* v___x_38_; 
lean_dec(v_h__1_32_);
v_head_36_ = lean_ctor_get(v_ys_31_, 0);
lean_inc(v_head_36_);
v_tail_37_ = lean_ctor_get(v_ys_31_, 1);
lean_inc(v_tail_37_);
lean_dec_ref_known(v_ys_31_, 2);
v___x_38_ = lean_apply_2(v_h__2_33_, v_head_36_, v_tail_37_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_InsertIdx_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_39_, lean_object* v_motive_40_, lean_object* v_ys_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
if (lean_obj_tag(v_ys_41_) == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_43_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_1(v_h__1_42_, v___x_44_);
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_42_);
v_head_46_ = lean_ctor_get(v_ys_41_, 0);
lean_inc(v_head_46_);
v_tail_47_ = lean_ctor_get(v_ys_41_, 1);
lean_inc(v_tail_47_);
lean_dec_ref_known(v_ys_41_, 2);
v___x_48_ = lean_apply_2(v_h__2_43_, v_head_46_, v_tail_47_);
return v___x_48_;
}
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_Modify(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Modify(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Modify(builtin);
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
res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_InsertIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_InsertIdx(builtin);
}
#ifdef __cplusplus
}
#endif
