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
static lean_once_cell_t l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_intZero_25_; uint8_t v_isNeg_26_; 
v_intZero_25_ = lean_obj_once(&l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___redArg___closed__0);
v_isNeg_26_ = lean_int_dec_lt(v_x_21_, v_intZero_25_);
if (v_isNeg_26_ == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_24_);
v_a_27_ = lean_nat_abs(v_x_21_);
v___x_28_ = lean_apply_2(v_h__1_23_, v_a_27_, v_x_22_);
return v___x_28_;
}
else
{
lean_object* v_abs_29_; lean_object* v_one_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_23_);
v_abs_29_ = lean_nat_abs(v_x_21_);
v_one_30_ = lean_unsigned_to_nat(1u);
v_a_31_ = lean_nat_sub(v_abs_29_, v_one_30_);
lean_dec(v_abs_29_);
v___x_32_ = lean_apply_2(v_h__2_24_, v_a_31_, v_x_22_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter___boxed(lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_shiftRight_match__1_splitter(v_motive_33_, v_x_34_, v_x_35_, v_h__1_36_, v_h__2_37_);
lean_dec(v_x_34_);
return v_res_38_;
}
}
static lean_object* _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_39_; lean_object* v_intZero_40_; 
v_natZero_39_ = lean_unsigned_to_nat(0u);
v_intZero_40_ = lean_nat_to_int(v_natZero_39_);
return v_intZero_40_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg(lean_object* v_x_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
lean_object* v_intZero_44_; uint8_t v_isNeg_45_; 
v_intZero_44_ = lean_obj_once(&l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0);
v_isNeg_45_ = lean_int_dec_lt(v_x_41_, v_intZero_44_);
if (v_isNeg_45_ == 0)
{
lean_object* v_a_46_; lean_object* v___x_47_; 
lean_dec(v_h__2_43_);
v_a_46_ = lean_nat_abs(v_x_41_);
v___x_47_ = lean_apply_1(v_h__1_42_, v_a_46_);
return v___x_47_;
}
else
{
lean_object* v_abs_48_; lean_object* v_one_49_; lean_object* v_a_50_; lean_object* v___x_51_; 
lean_dec(v_h__1_42_);
v_abs_48_ = lean_nat_abs(v_x_41_);
v_one_49_ = lean_unsigned_to_nat(1u);
v_a_50_ = lean_nat_sub(v_abs_48_, v_one_49_);
lean_dec(v_abs_48_);
v___x_51_ = lean_apply_1(v_h__2_43_, v_a_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___boxed(lean_object* v_x_52_, lean_object* v_h__1_53_, lean_object* v_h__2_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg(v_x_52_, v_h__1_53_, v_h__2_54_);
lean_dec(v_x_52_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter(lean_object* v_motive_56_, lean_object* v_x_57_, lean_object* v_h__1_58_, lean_object* v_h__2_59_){
_start:
{
lean_object* v_intZero_60_; uint8_t v_isNeg_61_; 
v_intZero_60_ = lean_obj_once(&l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0, &l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___redArg___closed__0);
v_isNeg_61_ = lean_int_dec_lt(v_x_57_, v_intZero_60_);
if (v_isNeg_61_ == 0)
{
lean_object* v_a_62_; lean_object* v___x_63_; 
lean_dec(v_h__2_59_);
v_a_62_ = lean_nat_abs(v_x_57_);
v___x_63_ = lean_apply_1(v_h__1_58_, v_a_62_);
return v___x_63_;
}
else
{
lean_object* v_abs_64_; lean_object* v_one_65_; lean_object* v_a_66_; lean_object* v___x_67_; 
lean_dec(v_h__1_58_);
v_abs_64_ = lean_nat_abs(v_x_57_);
v_one_65_ = lean_unsigned_to_nat(1u);
v_a_66_ = lean_nat_sub(v_abs_64_, v_one_65_);
lean_dec(v_abs_64_);
v___x_67_ = lean_apply_1(v_h__2_59_, v_a_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter___boxed(lean_object* v_motive_68_, lean_object* v_x_69_, lean_object* v_h__1_70_, lean_object* v_h__2_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Init_Data_Int_Bitwise_Lemmas_0__Int_not_match__1_splitter(v_motive_68_, v_x_69_, v_h__1_70_, v_h__2_71_);
lean_dec(v_x_69_);
return v_res_72_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Bitwise_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
