// Lean compiler output
// Module: Init.Data.Rat.Lemmas
// Imports: public import Init.Data.Rat.Basic public import Init.Data.Int.Gcd import Init.ByCases import Init.Data.Bool import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.Pow import Init.Data.Nat.Dvd import Init.Omega import Init.TacticsExtra
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
static lean_once_cell_t l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_h__1_5_, lean_object* v_h__2_6_){
_start:
{
lean_object* v_intZero_7_; uint8_t v_isNeg_8_; 
v_intZero_7_ = lean_obj_once(&l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0, &l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0);
v_isNeg_8_ = lean_int_dec_lt(v_x_4_, v_intZero_7_);
if (v_isNeg_8_ == 0)
{
lean_object* v_a_9_; lean_object* v___x_10_; 
lean_dec(v_h__2_6_);
v_a_9_ = lean_nat_abs(v_x_4_);
v___x_10_ = lean_apply_2(v_h__1_5_, v_x_3_, v_a_9_);
return v___x_10_;
}
else
{
lean_object* v_abs_11_; lean_object* v_one_12_; lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_5_);
v_abs_11_ = lean_nat_abs(v_x_4_);
v_one_12_ = lean_unsigned_to_nat(1u);
v_a_13_ = lean_nat_sub(v_abs_11_, v_one_12_);
lean_dec(v_abs_11_);
v___x_14_ = lean_apply_2(v_h__2_6_, v_x_3_, v_a_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___boxed(lean_object* v_x_15_, lean_object* v_x_16_, lean_object* v_h__1_17_, lean_object* v_h__2_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg(v_x_15_, v_x_16_, v_h__1_17_, v_h__2_18_);
lean_dec(v_x_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(lean_object* v_motive_20_, lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_h__1_23_, lean_object* v_h__2_24_){
_start:
{
lean_object* v_intZero_25_; uint8_t v_isNeg_26_; 
v_intZero_25_ = lean_obj_once(&l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0, &l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0_once, _init_l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___redArg___closed__0);
v_isNeg_26_ = lean_int_dec_lt(v_x_22_, v_intZero_25_);
if (v_isNeg_26_ == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; 
lean_dec(v_h__2_24_);
v_a_27_ = lean_nat_abs(v_x_22_);
v___x_28_ = lean_apply_2(v_h__1_23_, v_x_21_, v_a_27_);
return v___x_28_;
}
else
{
lean_object* v_abs_29_; lean_object* v_one_30_; lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__1_23_);
v_abs_29_ = lean_nat_abs(v_x_22_);
v_one_30_ = lean_unsigned_to_nat(1u);
v_a_31_ = lean_nat_sub(v_abs_29_, v_one_30_);
lean_dec(v_abs_29_);
v___x_32_ = lean_apply_2(v_h__2_24_, v_x_21_, v_a_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter___boxed(lean_object* v_motive_33_, lean_object* v_x_34_, lean_object* v_x_35_, lean_object* v_h__1_36_, lean_object* v_h__2_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Init_Data_Rat_Lemmas_0__Rat_divInt_match__3_splitter(v_motive_33_, v_x_34_, v_x_35_, v_h__1_36_, v_h__2_37_);
lean_dec(v_x_35_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn___redArg(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
lean_object* v_num_41_; lean_object* v_den_42_; lean_object* v___x_43_; 
v_num_41_ = lean_ctor_get(v_x_39_, 0);
lean_inc(v_num_41_);
v_den_42_ = lean_ctor_get(v_x_39_, 1);
lean_inc(v_den_42_);
lean_dec_ref(v_x_39_);
v___x_43_ = lean_apply_4(v_x_40_, v_num_41_, v_den_42_, lean_box(0), lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn(lean_object* v_C_44_, lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Rat_numDenCasesOn___redArg(v_x_45_, v_x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg___lam__0(lean_object* v_H_48_, lean_object* v_n_49_, lean_object* v_d_50_, lean_object* v_h_51_, lean_object* v_x_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_3(v_H_48_, v_n_49_, v_d_50_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27___redArg(lean_object* v_a_54_, lean_object* v_H_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___x_57_; 
v___f_56_ = lean_alloc_closure((void*)(l_Rat_numDenCasesOn_x27___redArg___lam__0), 5, 1);
lean_closure_set(v___f_56_, 0, v_H_55_);
v___x_57_ = l_Rat_numDenCasesOn___redArg(v_a_54_, v___f_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27(lean_object* v_C_58_, lean_object* v_a_59_, lean_object* v_H_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Rat_numDenCasesOn_x27___redArg(v_a_59_, v_H_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg___lam__0(lean_object* v_H_62_, lean_object* v_n_63_, lean_object* v_d_64_, lean_object* v_h_65_, lean_object* v_h_x27_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_apply_4(v_H_62_, v_n_63_, v_d_64_, lean_box(0), lean_box(0));
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27___redArg(lean_object* v_a_68_, lean_object* v_H_69_){
_start:
{
lean_object* v___f_70_; lean_object* v___x_71_; 
v___f_70_ = lean_alloc_closure((void*)(l_Rat_numDenCasesOn_x27_x27___redArg___lam__0), 5, 1);
lean_closure_set(v___f_70_, 0, v_H_69_);
v___x_71_ = l_Rat_numDenCasesOn___redArg(v_a_68_, v___f_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Rat_numDenCasesOn_x27_x27(lean_object* v_C_72_, lean_object* v_a_73_, lean_object* v_H_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Rat_numDenCasesOn_x27_x27___redArg(v_a_73_, v_H_74_);
return v___x_75_;
}
}
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Rat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Rat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Rat_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Rat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Rat_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
