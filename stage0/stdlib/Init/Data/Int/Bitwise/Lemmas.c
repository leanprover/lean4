// Lean compiler output
// Module: Init.Data.Int.Bitwise.Lemmas
// Imports: public import Init.Data.Int.Bitwise.Basic import all Init.Data.Int.Bitwise.Basic public import Init.Data.Int.DivMod.Basic import Init.ByCases import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases
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
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_h__1_5_, lean_object* v_h__2_6_){
_start:
{
lean_object* v_intZero_7_; uint8_t v_isNeg_8_; 
v_intZero_7_ = lean_obj_once(&l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0);
v_isNeg_8_ = lean_int_dec_lt(v_x_3_, v_intZero_7_);
if (v_isNeg_8_ == 0)
{
lean_object* v_a_9_; lean_object* v___x_10_; 
lean_dec(v_h__2_6_);
v_a_9_ = lean_nat_abs(v_x_3_);
v___x_10_ = lean_apply_2(v_h__1_5_, v_a_9_, v_x_4_);
return v___x_10_;
}
else
{
lean_object* v_abs_11_; lean_object* v_one_12_; lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_5_);
v_abs_11_ = lean_nat_abs(v_x_3_);
v_one_12_ = lean_unsigned_to_nat(1u);
v_a_13_ = lean_nat_sub(v_abs_11_, v_one_12_);
lean_dec(v_abs_11_);
v___x_14_ = lean_apply_2(v_h__2_6_, v_a_13_, v_x_4_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___boxed(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(v_x_15_, v_x_16_, v_h__1_17_, v_h__2_18_);
lean_dec(v_x_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg(v_x_21_, v_x_22_, v_h__1_23_, v_h__2_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___boxed(lean_object* v_motive_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v_h__1_29_, lean_object* v_h__2_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(v_motive_26_, v_x_27_, v_x_28_, v_h__1_29_, v_h__2_30_);
lean_dec(v_x_27_);
return v_res_31_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
