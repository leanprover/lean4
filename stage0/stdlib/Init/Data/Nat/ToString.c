// Lean compiler output
// Module: Init.Data.Nat.ToString
// Imports: public import Init.Data.Repr public import Init.Data.Char.Basic public import Init.Data.ToString.Basic public import Init.Data.String.Basic import Init.NotationExtra import all Init.Data.Repr import Init.Omega import Init.RCases import Init.Data.Nat.Lemmas import Init.Data.Nat.Bitwise import Init.Data.Nat.Simproc import Init.WFTactics import Init.Data.Char.Lemmas import Init.Data.Nat.Div.Lemmas
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
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Nat_ofDigitChars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Nat_ofDigitChars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_ofDigitChars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_ofDigitChars___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_x_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_1_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_object* v___x_8_; 
lean_dec(v_h__2_5_);
v___x_8_ = lean_apply_2(v_h__1_4_, v_x_2_, v_x_3_);
return v___x_8_;
}
else
{
lean_object* v_one_9_; lean_object* v_n_10_; lean_object* v___x_11_; 
lean_dec(v_h__1_4_);
v_one_9_ = lean_unsigned_to_nat(1u);
v_n_10_ = lean_nat_sub(v_x_1_, v_one_9_);
v___x_11_ = lean_apply_3(v_h__2_5_, v_n_10_, v_x_2_, v_x_3_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg___boxed(lean_object* v_x_12_, lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg(v_x_12_, v_x_13_, v_x_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_x_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter(lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
lean_object* v_zero_24_; uint8_t v_isZero_25_; 
v_zero_24_ = lean_unsigned_to_nat(0u);
v_isZero_25_ = lean_nat_dec_eq(v_x_19_, v_zero_24_);
if (v_isZero_25_ == 1)
{
lean_object* v___x_26_; 
lean_dec(v_h__2_23_);
v___x_26_ = lean_apply_2(v_h__1_22_, v_x_20_, v_x_21_);
return v___x_26_;
}
else
{
lean_object* v_one_27_; lean_object* v_n_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_22_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_n_28_ = lean_nat_sub(v_x_19_, v_one_27_);
v___x_29_ = lean_apply_3(v_h__2_23_, v_n_28_, v_x_20_, v_x_21_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___boxed(lean_object* v_motive_30_, lean_object* v_x_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter(v_motive_30_, v_x_31_, v_x_32_, v_x_33_, v_h__1_34_, v_h__2_35_);
lean_dec(v_x_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Nat_ofDigitChars_spec__0(lean_object* v_b_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
return v_x_38_;
}
else
{
lean_object* v_head_40_; lean_object* v_tail_41_; lean_object* v___x_42_; uint32_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v_head_40_ = lean_ctor_get(v_x_39_, 0);
v_tail_41_ = lean_ctor_get(v_x_39_, 1);
v___x_42_ = lean_nat_mul(v_b_37_, v_x_38_);
lean_dec(v_x_38_);
v___x_43_ = lean_unbox_uint32(v_head_40_);
v___x_44_ = lean_uint32_to_nat(v___x_43_);
v___x_45_ = lean_unsigned_to_nat(48u);
v___x_46_ = lean_nat_sub(v___x_44_, v___x_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_nat_add(v___x_42_, v___x_46_);
lean_dec(v___x_46_);
lean_dec(v___x_42_);
v_x_38_ = v___x_47_;
v_x_39_ = v_tail_41_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Nat_ofDigitChars_spec__0___boxed(lean_object* v_b_49_, lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_List_foldl___at___00Nat_ofDigitChars_spec__0(v_b_49_, v_x_50_, v_x_51_);
lean_dec(v_x_51_);
lean_dec(v_b_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Nat_ofDigitChars(lean_object* v_b_53_, lean_object* v_l_54_, lean_object* v_init_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_List_foldl___at___00Nat_ofDigitChars_spec__0(v_b_53_, v_init_55_, v_l_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Nat_ofDigitChars___boxed(lean_object* v_b_57_, lean_object* v_l_58_, lean_object* v_init_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Nat_ofDigitChars(v_b_57_, v_l_58_, v_init_59_);
lean_dec(v_l_58_);
lean_dec(v_b_57_);
return v_res_60_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_ToString(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_ToString(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Simproc(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Div_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_ToString(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_ToString(builtin);
}
#ifdef __cplusplus
}
#endif
