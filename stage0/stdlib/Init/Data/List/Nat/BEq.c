// Lean compiler output
// Module: Init.Data.List.Nat.BEq
// Imports: public import Init.Data.Nat.Lemmas import Init.Data.List.Lemmas import Init.Data.Bool
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_BEq_0__List_isEqv_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_BEq_0__List_isEqv_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_BEq_0__List_isEqv_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_, lean_object* v_h__3_6_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_dec(v_h__2_5_);
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_7_; 
lean_dec(v_h__3_6_);
v___x_7_ = lean_apply_1(v_h__1_4_, v_x_3_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_h__1_4_);
v___x_8_ = lean_apply_5(v_h__3_6_, v_x_1_, v_x_2_, v_x_3_, lean_box(0), lean_box(0));
return v___x_8_;
}
}
else
{
lean_dec(v_h__1_4_);
if (lean_obj_tag(v_x_2_) == 1)
{
lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v_head_11_; lean_object* v_tail_12_; lean_object* v___x_13_; 
lean_dec(v_h__3_6_);
v_head_9_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_9_);
v_tail_10_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_10_);
lean_dec_ref_known(v_x_1_, 2);
v_head_11_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_11_);
v_tail_12_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_12_);
lean_dec_ref_known(v_x_2_, 2);
v___x_13_ = lean_apply_5(v_h__2_5_, v_head_9_, v_tail_10_, v_head_11_, v_tail_12_, v_x_3_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; 
lean_dec(v_h__2_5_);
v___x_14_ = lean_apply_5(v_h__3_6_, v_x_1_, v_x_2_, v_x_3_, lean_box(0), lean_box(0));
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_BEq_0__List_isEqv_match__1_splitter(lean_object* v_00_u03b1_15_, lean_object* v_motive_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_, lean_object* v_h__3_22_){
_start:
{
if (lean_obj_tag(v_x_17_) == 0)
{
lean_dec(v_h__2_21_);
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_23_; 
lean_dec(v_h__3_22_);
v___x_23_ = lean_apply_1(v_h__1_20_, v_x_19_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
lean_dec(v_h__1_20_);
v___x_24_ = lean_apply_5(v_h__3_22_, v_x_17_, v_x_18_, v_x_19_, lean_box(0), lean_box(0));
return v___x_24_;
}
}
else
{
lean_dec(v_h__1_20_);
if (lean_obj_tag(v_x_18_) == 1)
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v_head_27_; lean_object* v_tail_28_; lean_object* v___x_29_; 
lean_dec(v_h__3_22_);
v_head_25_ = lean_ctor_get(v_x_17_, 0);
lean_inc(v_head_25_);
v_tail_26_ = lean_ctor_get(v_x_17_, 1);
lean_inc(v_tail_26_);
lean_dec_ref_known(v_x_17_, 2);
v_head_27_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_head_27_);
v_tail_28_ = lean_ctor_get(v_x_18_, 1);
lean_inc(v_tail_28_);
lean_dec_ref_known(v_x_18_, 2);
v___x_29_ = lean_apply_5(v_h__2_21_, v_head_25_, v_tail_26_, v_head_27_, v_tail_28_, v_x_19_);
return v___x_29_;
}
else
{
lean_object* v___x_30_; 
lean_dec(v_h__2_21_);
v___x_30_ = lean_apply_5(v_h__3_22_, v_x_17_, v_x_18_, v_x_19_, lean_box(0), lean_box(0));
return v___x_30_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_BEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_BEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_BEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_BEq(builtin);
}
#ifdef __cplusplus
}
#endif
