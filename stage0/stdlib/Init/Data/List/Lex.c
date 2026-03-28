// Lean compiler output
// Module: Init.Data.List.Lex
// Imports: import Init.Data.Order.Lemmas public import Init.Data.BEq public import Init.Data.Order.Classes public import Init.Ext public import Init.NotationExtra import Init.ByCases import Init.Data.Bool import Init.Data.List.Nat.TakeDrop import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas import Init.TacticsExtra
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
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object* v_00_u03b1_1_, lean_object* v_inst_2_, lean_object* v_inst_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object* v_l_u2081_11_, lean_object* v_l_u2082_12_, lean_object* v_h__1_13_, lean_object* v_h__2_14_, lean_object* v_h__3_15_){
_start:
{
if (lean_obj_tag(v_l_u2081_11_) == 0)
{
lean_dec(v_h__3_15_);
if (lean_obj_tag(v_l_u2082_12_) == 0)
{
lean_object* v___x_16_; 
lean_dec(v_h__1_13_);
v___x_16_ = lean_apply_1(v_h__2_14_, v_l_u2082_12_);
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v___x_19_; 
lean_dec(v_h__2_14_);
v_head_17_ = lean_ctor_get(v_l_u2082_12_, 0);
lean_inc(v_head_17_);
v_tail_18_ = lean_ctor_get(v_l_u2082_12_, 1);
lean_inc(v_tail_18_);
lean_dec_ref(v_l_u2082_12_);
v___x_19_ = lean_apply_2(v_h__1_13_, v_head_17_, v_tail_18_);
return v___x_19_;
}
}
else
{
lean_dec(v_h__1_13_);
if (lean_obj_tag(v_l_u2082_12_) == 0)
{
lean_object* v___x_20_; 
lean_dec(v_h__3_15_);
v___x_20_ = lean_apply_1(v_h__2_14_, v_l_u2081_11_);
return v___x_20_;
}
else
{
lean_object* v_head_21_; lean_object* v_tail_22_; lean_object* v_head_23_; lean_object* v_tail_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_14_);
v_head_21_ = lean_ctor_get(v_l_u2081_11_, 0);
lean_inc(v_head_21_);
v_tail_22_ = lean_ctor_get(v_l_u2081_11_, 1);
lean_inc(v_tail_22_);
lean_dec_ref(v_l_u2081_11_);
v_head_23_ = lean_ctor_get(v_l_u2082_12_, 0);
lean_inc(v_head_23_);
v_tail_24_ = lean_ctor_get(v_l_u2082_12_, 1);
lean_inc(v_tail_24_);
lean_dec_ref(v_l_u2082_12_);
v___x_25_ = lean_apply_4(v_h__3_15_, v_head_21_, v_tail_22_, v_head_23_, v_tail_24_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object* v_00_u03b1_26_, lean_object* v_motive_27_, lean_object* v_l_u2081_28_, lean_object* v_l_u2082_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_, lean_object* v_h__3_32_){
_start:
{
if (lean_obj_tag(v_l_u2081_28_) == 0)
{
lean_dec(v_h__3_32_);
if (lean_obj_tag(v_l_u2082_29_) == 0)
{
lean_object* v___x_33_; 
lean_dec(v_h__1_30_);
v___x_33_ = lean_apply_1(v_h__2_31_, v_l_u2082_29_);
return v___x_33_;
}
else
{
lean_object* v_head_34_; lean_object* v_tail_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_31_);
v_head_34_ = lean_ctor_get(v_l_u2082_29_, 0);
lean_inc(v_head_34_);
v_tail_35_ = lean_ctor_get(v_l_u2082_29_, 1);
lean_inc(v_tail_35_);
lean_dec_ref(v_l_u2082_29_);
v___x_36_ = lean_apply_2(v_h__1_30_, v_head_34_, v_tail_35_);
return v___x_36_;
}
}
else
{
lean_dec(v_h__1_30_);
if (lean_obj_tag(v_l_u2082_29_) == 0)
{
lean_object* v___x_37_; 
lean_dec(v_h__3_32_);
v___x_37_ = lean_apply_1(v_h__2_31_, v_l_u2081_28_);
return v___x_37_;
}
else
{
lean_object* v_head_38_; lean_object* v_tail_39_; lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_42_; 
lean_dec(v_h__2_31_);
v_head_38_ = lean_ctor_get(v_l_u2081_28_, 0);
lean_inc(v_head_38_);
v_tail_39_ = lean_ctor_get(v_l_u2081_28_, 1);
lean_inc(v_tail_39_);
lean_dec_ref(v_l_u2081_28_);
v_head_40_ = lean_ctor_get(v_l_u2082_29_, 0);
lean_inc(v_head_40_);
v_tail_41_ = lean_ctor_get(v_l_u2082_29_, 1);
lean_inc(v_tail_41_);
lean_dec_ref(v_l_u2082_29_);
v___x_42_ = lean_apply_4(v_h__3_32_, v_head_38_, v_tail_39_, v_head_40_, v_tail_41_);
return v___x_42_;
}
}
}
}
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BEq(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_BEq(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Lex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Lex(builtin);
}
#ifdef __cplusplus
}
#endif
