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
LEAN_EXPORT lean_object* l_List_instTransLt___redArg();
LEAN_EXPORT lean_object* l_List_instTransLt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg();
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransLt___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLt___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_List_instTransLt___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLt(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg(){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_box(0);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_List_instTransLeOfIsLinearOrderOfLawfulOrderLT(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_inst_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter___redArg(lean_object* v_l_u2081_19_, lean_object* v_l_u2082_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_, lean_object* v_h__3_23_){
_start:
{
if (lean_obj_tag(v_l_u2081_19_) == 0)
{
lean_dec(v_h__3_23_);
if (lean_obj_tag(v_l_u2082_20_) == 0)
{
lean_object* v___x_24_; 
lean_dec(v_h__1_21_);
v___x_24_ = lean_apply_1(v_h__2_22_, v_l_u2082_20_);
return v___x_24_;
}
else
{
lean_object* v_head_25_; lean_object* v_tail_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_22_);
v_head_25_ = lean_ctor_get(v_l_u2082_20_, 0);
lean_inc(v_head_25_);
v_tail_26_ = lean_ctor_get(v_l_u2082_20_, 1);
lean_inc(v_tail_26_);
lean_dec_ref_known(v_l_u2082_20_, 2);
v___x_27_ = lean_apply_2(v_h__1_21_, v_head_25_, v_tail_26_);
return v___x_27_;
}
}
else
{
lean_dec(v_h__1_21_);
if (lean_obj_tag(v_l_u2082_20_) == 0)
{
lean_object* v___x_28_; 
lean_dec(v_h__3_23_);
v___x_28_ = lean_apply_1(v_h__2_22_, v_l_u2081_19_);
return v___x_28_;
}
else
{
lean_object* v_head_29_; lean_object* v_tail_30_; lean_object* v_head_31_; lean_object* v_tail_32_; lean_object* v___x_33_; 
lean_dec(v_h__2_22_);
v_head_29_ = lean_ctor_get(v_l_u2081_19_, 0);
lean_inc(v_head_29_);
v_tail_30_ = lean_ctor_get(v_l_u2081_19_, 1);
lean_inc(v_tail_30_);
lean_dec_ref_known(v_l_u2081_19_, 2);
v_head_31_ = lean_ctor_get(v_l_u2082_20_, 0);
lean_inc(v_head_31_);
v_tail_32_ = lean_ctor_get(v_l_u2082_20_, 1);
lean_inc(v_tail_32_);
lean_dec_ref_known(v_l_u2082_20_, 2);
v___x_33_ = lean_apply_4(v_h__3_23_, v_head_29_, v_tail_30_, v_head_31_, v_tail_32_);
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Lex_0__List_lex_match__1_splitter(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_l_u2081_36_, lean_object* v_l_u2082_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_, lean_object* v_h__3_40_){
_start:
{
if (lean_obj_tag(v_l_u2081_36_) == 0)
{
lean_dec(v_h__3_40_);
if (lean_obj_tag(v_l_u2082_37_) == 0)
{
lean_object* v___x_41_; 
lean_dec(v_h__1_38_);
v___x_41_ = lean_apply_1(v_h__2_39_, v_l_u2082_37_);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__2_39_);
v_head_42_ = lean_ctor_get(v_l_u2082_37_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_l_u2082_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref_known(v_l_u2082_37_, 2);
v___x_44_ = lean_apply_2(v_h__1_38_, v_head_42_, v_tail_43_);
return v___x_44_;
}
}
else
{
lean_dec(v_h__1_38_);
if (lean_obj_tag(v_l_u2082_37_) == 0)
{
lean_object* v___x_45_; 
lean_dec(v_h__3_40_);
v___x_45_ = lean_apply_1(v_h__2_39_, v_l_u2081_36_);
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v_head_48_; lean_object* v_tail_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_39_);
v_head_46_ = lean_ctor_get(v_l_u2081_36_, 0);
lean_inc(v_head_46_);
v_tail_47_ = lean_ctor_get(v_l_u2081_36_, 1);
lean_inc(v_tail_47_);
lean_dec_ref_known(v_l_u2081_36_, 2);
v_head_48_ = lean_ctor_get(v_l_u2082_37_, 0);
lean_inc(v_head_48_);
v_tail_49_ = lean_ctor_get(v_l_u2082_37_, 1);
lean_inc(v_tail_49_);
lean_dec_ref_known(v_l_u2082_37_, 2);
v___x_50_ = lean_apply_4(v_h__3_40_, v_head_46_, v_tail_47_, v_head_48_, v_tail_49_);
return v___x_50_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Lex(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
