// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Pred
// Imports: public import Init.Data.String.Pattern.Pred public import Init.Data.String.Lemmas.Pattern.Basic public import Init.Data.String.Slice public import Init.Data.String.Search import all Init.Data.String.Slice import all Init.Data.String.Pattern.Pred import all Init.Data.String.Search import Init.Data.Option.Lemmas import Init.Data.String.Lemmas.Basic import Init.Data.String.Lemmas.Order import Init.Data.Order.Lemmas import Init.Data.String.OrderInstances import Init.Omega
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
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_instForwardPatternModelForallCharBool(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_instForwardPatternModelForallCharBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_Decidable_instForwardPatternModelForallCharPropOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_Decidable_instForwardPatternModelForallCharPropOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_instForwardPatternModelForallCharBool(lean_object* v_p_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_instForwardPatternModelForallCharBool___boxed(lean_object* v_p_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_String_Slice_Pattern_Model_CharPred_instForwardPatternModelForallCharBool(v_p_3_);
lean_dec_ref(v_p_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_Decidable_instForwardPatternModelForallCharPropOfDecidablePred(lean_object* v_p_5_, lean_object* v_inst_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_Model_CharPred_Decidable_instForwardPatternModelForallCharPropOfDecidablePred___boxed(lean_object* v_p_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_Slice_Pattern_Model_CharPred_Decidable_instForwardPatternModelForallCharPropOfDecidablePred(v_p_8_, v_inst_9_);
lean_dec_ref(v_inst_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_11_) == 1)
{
lean_object* v_val_14_; lean_object* v___x_15_; 
lean_dec(v_h__2_13_);
v_val_14_ = lean_ctor_get(v_x_11_, 0);
lean_inc(v_val_14_);
lean_dec_ref(v_x_11_);
v___x_15_ = lean_apply_1(v_h__1_12_, v_val_14_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; 
lean_dec(v_h__1_12_);
v___x_16_ = lean_apply_2(v_h__2_13_, v_x_11_, lean_box(0));
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_17_, lean_object* v_pos_18_, lean_object* v_motive_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
if (lean_obj_tag(v_x_20_) == 1)
{
lean_object* v_val_23_; lean_object* v___x_24_; 
lean_dec(v_h__2_22_);
v_val_23_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_23_);
lean_dec_ref(v_x_20_);
v___x_24_ = lean_apply_1(v_h__1_21_, v_val_23_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; 
lean_dec(v_h__1_21_);
v___x_25_ = lean_apply_2(v_h__2_22_, v_x_20_, lean_box(0));
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_26_, lean_object* v_pos_27_, lean_object* v_motive_28_, lean_object* v_x_29_, lean_object* v_h__1_30_, lean_object* v_h__2_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_26_, v_pos_27_, v_motive_28_, v_x_29_, v_h__1_30_, v_h__2_31_);
lean_dec(v_pos_27_);
lean_dec_ref(v_s_26_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter___redArg(lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_33_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_37_; 
lean_dec(v_h__2_35_);
v_val_36_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_val_36_);
lean_dec_ref(v_x_33_);
v___x_37_ = lean_apply_1(v_h__1_34_, v_val_36_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; 
lean_dec(v_h__1_34_);
v___x_38_ = lean_apply_2(v_h__2_35_, v_x_33_, lean_box(0));
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter(lean_object* v_s_39_, lean_object* v_pos_40_, lean_object* v_motive_41_, lean_object* v_x_42_, lean_object* v_h__1_43_, lean_object* v_h__2_44_){
_start:
{
if (lean_obj_tag(v_x_42_) == 1)
{
lean_object* v_val_45_; lean_object* v___x_46_; 
lean_dec(v_h__2_44_);
v_val_45_ = lean_ctor_get(v_x_42_, 0);
lean_inc(v_val_45_);
lean_dec_ref(v_x_42_);
v___x_46_ = lean_apply_1(v_h__1_43_, v_val_45_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; 
lean_dec(v_h__1_43_);
v___x_47_ = lean_apply_2(v_h__2_44_, v_x_42_, lean_box(0));
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter___boxed(lean_object* v_s_48_, lean_object* v_pos_49_, lean_object* v_motive_50_, lean_object* v_x_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Init_Data_String_Lemmas_Pattern_Pred_0__String_Slice_Pos_revSkipWhile_match__1_splitter(v_s_48_, v_pos_49_, v_motive_50_, v_x_51_, v_h__1_52_, v_h__2_53_);
lean_dec(v_pos_49_);
lean_dec_ref(v_s_48_);
return v_res_54_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern_Pred(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Pattern_Pred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Pattern_Pred(builtin);
}
#ifdef __cplusplus
}
#endif
