// Lean compiler output
// Module: Init.Data.Int.Cooper
// Imports: public import Init.Data.Int.Gcd import Init.Data.Int.DivMod.Lemmas import Init.Omega import Init.RCases
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
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_lcm(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Cooper_resolve__left_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_add__of__le___redArg(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_int_sub(v_b_2_, v_a_1_);
v___x_4_ = l_Int_toNat(v___x_3_);
lean_dec(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Int_add__of__le___redArg___boxed(lean_object* v_a_5_, lean_object* v_b_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Int_add__of__le___redArg(v_a_5_, v_b_6_);
lean_dec(v_b_6_);
lean_dec(v_a_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Int_add__of__le(lean_object* v_a_8_, lean_object* v_b_9_, lean_object* v_h_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Int_add__of__le___redArg(v_a_8_, v_b_9_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Int_add__of__le___boxed(lean_object* v_a_12_, lean_object* v_b_13_, lean_object* v_h_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Int_add__of__le(v_a_12_, v_b_13_, v_h_14_);
lean_dec(v_b_13_);
lean_dec(v_a_12_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Int_Cooper_resolve__left_spec__0(lean_object* v_a_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_nat_to_int(v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left(lean_object* v_a_18_, lean_object* v_c_19_, lean_object* v_d_20_, lean_object* v_p_21_, lean_object* v_x_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_23_ = lean_int_mul(v_a_18_, v_x_22_);
v___x_24_ = lean_int_sub(v___x_23_, v_p_21_);
lean_dec(v___x_23_);
v___x_25_ = lean_int_mul(v_a_18_, v_d_20_);
v___x_26_ = l_Int_gcd(v___x_25_, v_c_19_);
v___x_27_ = lean_nat_to_int(v___x_26_);
v___x_28_ = lean_int_ediv(v___x_25_, v___x_27_);
lean_dec(v___x_27_);
lean_dec(v___x_25_);
v___x_29_ = l_Int_lcm(v_a_18_, v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = lean_nat_to_int(v___x_29_);
v___x_31_ = lean_int_emod(v___x_24_, v___x_30_);
lean_dec(v___x_30_);
lean_dec(v___x_24_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left___boxed(lean_object* v_a_32_, lean_object* v_c_33_, lean_object* v_d_34_, lean_object* v_p_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Int_Cooper_resolve__left(v_a_32_, v_c_33_, v_d_34_, v_p_35_, v_x_36_);
lean_dec(v_x_36_);
lean_dec(v_p_35_);
lean_dec(v_d_34_);
lean_dec(v_c_33_);
lean_dec(v_a_32_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___redArg(lean_object* v_a_38_, lean_object* v_c_39_, lean_object* v_d_40_, lean_object* v_p_41_, lean_object* v_x_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_43_ = lean_int_mul(v_a_38_, v_x_42_);
v___x_44_ = l_Int_add__of__le___redArg(v_p_41_, v___x_43_);
lean_dec(v___x_43_);
v___x_45_ = lean_int_mul(v_a_38_, v_d_40_);
v___x_46_ = l_Int_gcd(v___x_45_, v_c_39_);
v___x_47_ = lean_nat_to_int(v___x_46_);
v___x_48_ = lean_int_ediv(v___x_45_, v___x_47_);
lean_dec(v___x_47_);
lean_dec(v___x_45_);
v___x_49_ = l_Int_lcm(v_a_38_, v___x_48_);
lean_dec(v___x_48_);
v___x_50_ = lean_nat_mod(v___x_44_, v___x_49_);
lean_dec(v___x_49_);
lean_dec(v___x_44_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___redArg___boxed(lean_object* v_a_51_, lean_object* v_c_52_, lean_object* v_d_53_, lean_object* v_p_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Int_Cooper_resolve__left_x27___redArg(v_a_51_, v_c_52_, v_d_53_, v_p_54_, v_x_55_);
lean_dec(v_x_55_);
lean_dec(v_p_54_);
lean_dec(v_d_53_);
lean_dec(v_c_52_);
lean_dec(v_a_51_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27(lean_object* v_a_57_, lean_object* v_c_58_, lean_object* v_d_59_, lean_object* v_p_60_, lean_object* v_x_61_, lean_object* v_h_u2081_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Int_Cooper_resolve__left_x27___redArg(v_a_57_, v_c_58_, v_d_59_, v_p_60_, v_x_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left_x27___boxed(lean_object* v_a_64_, lean_object* v_c_65_, lean_object* v_d_66_, lean_object* v_p_67_, lean_object* v_x_68_, lean_object* v_h_u2081_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Int_Cooper_resolve__left_x27(v_a_64_, v_c_65_, v_d_66_, v_p_67_, v_x_68_, v_h_u2081_69_);
lean_dec(v_x_68_);
lean_dec(v_p_67_);
lean_dec(v_d_66_);
lean_dec(v_c_65_);
lean_dec(v_a_64_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv(lean_object* v_a_71_, lean_object* v_p_72_, lean_object* v_k_73_){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_int_add(v_k_73_, v_p_72_);
v___x_75_ = lean_int_ediv(v___x_74_, v_a_71_);
lean_dec(v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Int_Cooper_resolve__left__inv___boxed(lean_object* v_a_76_, lean_object* v_p_77_, lean_object* v_k_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Int_Cooper_resolve__left__inv(v_a_76_, v_p_77_, v_k_78_);
lean_dec(v_k_78_);
lean_dec(v_p_77_);
lean_dec(v_a_76_);
return v_res_79_;
}
}
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Int_Cooper(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Int_Cooper(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Int_Cooper(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Cooper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Int_Cooper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Int_Cooper(builtin);
}
#ifdef __cplusplus
}
#endif
