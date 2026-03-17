// Lean compiler output
// Module: Init.Data.List.Nat.Basic
// Imports: public import Init.Data.List.MinMax import Init.Data.Bool import Init.Data.List.Count import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.Data.Nat.MinMax import Init.Data.Option.Lemmas import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__2_3_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__1_2_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v_val_6_; lean_object* v___x_7_; 
lean_dec(v_h__1_2_);
v_val_6_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_val_6_);
lean_dec_ref(v_x_1_);
v___x_7_ = lean_apply_1(v_h__2_3_, v_val_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_x_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_List_Nat_Basic_0__List_filterMap_match__1_splitter___redArg(v_x_10_, v_h__1_11_, v_h__2_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter___redArg(lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_, lean_object* v_h__3_17_){
_start:
{
if (lean_obj_tag(v_x_14_) == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_h__3_17_);
lean_dec(v_h__2_16_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_h__1_15_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v_tail_20_; 
lean_dec(v_h__1_15_);
v_tail_20_ = lean_ctor_get(v_x_14_, 1);
if (lean_obj_tag(v_tail_20_) == 0)
{
lean_object* v_head_21_; lean_object* v___x_22_; 
lean_dec(v_h__3_17_);
v_head_21_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_21_);
lean_dec_ref(v_x_14_);
v___x_22_ = lean_apply_1(v_h__2_16_, v_head_21_);
return v___x_22_;
}
else
{
lean_object* v_head_23_; lean_object* v___x_24_; 
lean_inc(v_tail_20_);
lean_dec(v_h__2_16_);
v_head_23_ = lean_ctor_get(v_x_14_, 0);
lean_inc(v_head_23_);
lean_dec_ref(v_x_14_);
v___x_24_ = lean_apply_3(v_h__3_17_, v_head_23_, v_tail_20_, lean_box(0));
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_dropLast_match__1_splitter(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_h__1_28_, lean_object* v_h__2_29_, lean_object* v_h__3_30_){
_start:
{
if (lean_obj_tag(v_x_27_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_h__3_30_);
lean_dec(v_h__2_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_apply_1(v_h__1_28_, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v_tail_33_; 
lean_dec(v_h__1_28_);
v_tail_33_ = lean_ctor_get(v_x_27_, 1);
if (lean_obj_tag(v_tail_33_) == 0)
{
lean_object* v_head_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_30_);
v_head_34_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_34_);
lean_dec_ref(v_x_27_);
v___x_35_ = lean_apply_1(v_h__2_29_, v_head_34_);
return v___x_35_;
}
else
{
lean_object* v_head_36_; lean_object* v___x_37_; 
lean_inc(v_tail_33_);
lean_dec(v_h__2_29_);
v_head_36_ = lean_ctor_get(v_x_27_, 0);
lean_inc(v_head_36_);
lean_dec_ref(v_x_27_);
v___x_37_ = lean_apply_3(v_h__3_30_, v_head_36_, v_tail_33_, lean_box(0));
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(lean_object* v_x_38_, lean_object* v_x_39_, lean_object* v_h__1_40_, lean_object* v_h__2_41_, lean_object* v_h__3_42_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
lean_object* v___x_43_; 
lean_dec(v_h__3_42_);
lean_dec(v_h__2_41_);
v___x_43_ = lean_apply_1(v_h__1_40_, v_x_39_);
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v_zero_46_; uint8_t v_isZero_47_; 
lean_dec(v_h__1_40_);
v_head_44_ = lean_ctor_get(v_x_38_, 0);
lean_inc(v_head_44_);
v_tail_45_ = lean_ctor_get(v_x_38_, 1);
lean_inc(v_tail_45_);
lean_dec_ref(v_x_38_);
v_zero_46_ = lean_unsigned_to_nat(0u);
v_isZero_47_ = lean_nat_dec_eq(v_x_39_, v_zero_46_);
if (v_isZero_47_ == 1)
{
lean_object* v___x_48_; 
lean_dec(v_h__3_42_);
lean_dec(v_x_39_);
v___x_48_ = lean_apply_2(v_h__2_41_, v_head_44_, v_tail_45_);
return v___x_48_;
}
else
{
lean_object* v_one_49_; lean_object* v_n_50_; lean_object* v___x_51_; 
lean_dec(v_h__2_41_);
v_one_49_ = lean_unsigned_to_nat(1u);
v_n_50_ = lean_nat_sub(v_x_39_, v_one_49_);
lean_dec(v_x_39_);
v___x_51_ = lean_apply_3(v_h__3_42_, v_head_44_, v_tail_45_, v_n_50_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter(lean_object* v_00_u03b1_52_, lean_object* v_motive_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_, lean_object* v_h__3_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l___private_Init_Data_List_Nat_Basic_0__List_eraseIdx_match__1_splitter___redArg(v_x_54_, v_x_55_, v_h__1_56_, v_h__2_57_, v_h__3_58_);
return v___x_59_;
}
}
lean_object* runtime_initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
