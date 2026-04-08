// Lean compiler output
// Module: Init.Omega.Int
// Imports: public import Init.Data.Fin.Basic public import Init.Data.Int.DivMod.Basic public import Init.WF import Init.ByCases import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.PropLemmas
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
static lean_once_cell_t l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg(lean_object* v_n_3_, lean_object* v_h__1_4_, lean_object* v_h__2_5_){
_start:
{
lean_object* v_intZero_6_; uint8_t v_isNeg_7_; 
v_intZero_6_ = lean_obj_once(&l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0, &l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_7_ = lean_int_dec_lt(v_n_3_, v_intZero_6_);
if (v_isNeg_7_ == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; 
lean_dec(v_h__2_5_);
v_a_8_ = lean_nat_abs(v_n_3_);
v___x_9_ = lean_apply_1(v_h__1_4_, v_a_8_);
return v___x_9_;
}
else
{
lean_object* v_abs_10_; lean_object* v_one_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
lean_dec(v_h__1_4_);
v_abs_10_ = lean_nat_abs(v_n_3_);
v_one_11_ = lean_unsigned_to_nat(1u);
v_a_12_ = lean_nat_sub(v_abs_10_, v_one_11_);
lean_dec(v_abs_10_);
v___x_13_ = lean_apply_1(v_h__2_5_, v_a_12_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___boxed(lean_object* v_n_14_, lean_object* v_h__1_15_, lean_object* v_h__2_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg(v_n_14_, v_h__1_15_, v_h__2_16_);
lean_dec(v_n_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter(lean_object* v_motive_18_, lean_object* v_n_19_, lean_object* v_h__1_20_, lean_object* v_h__2_21_){
_start:
{
lean_object* v_intZero_22_; uint8_t v_isNeg_23_; 
v_intZero_22_ = lean_obj_once(&l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0, &l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0_once, _init_l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___redArg___closed__0);
v_isNeg_23_ = lean_int_dec_lt(v_n_19_, v_intZero_22_);
if (v_isNeg_23_ == 0)
{
lean_object* v_a_24_; lean_object* v___x_25_; 
lean_dec(v_h__2_21_);
v_a_24_ = lean_nat_abs(v_n_19_);
v___x_25_ = lean_apply_1(v_h__1_20_, v_a_24_);
return v___x_25_;
}
else
{
lean_object* v_abs_26_; lean_object* v_one_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
lean_dec(v_h__1_20_);
v_abs_26_ = lean_nat_abs(v_n_19_);
v_one_27_ = lean_unsigned_to_nat(1u);
v_a_28_ = lean_nat_sub(v_abs_26_, v_one_27_);
lean_dec(v_abs_26_);
v___x_29_ = lean_apply_1(v_h__2_21_, v_a_28_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_Int_0__Int_neg_match__1_splitter___boxed(lean_object* v_motive_30_, lean_object* v_n_31_, lean_object* v_h__1_32_, lean_object* v_h__2_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l___private_Init_Omega_Int_0__Int_neg_match__1_splitter(v_motive_30_, v_n_31_, v_h__1_32_, v_h__2_33_);
lean_dec(v_n_31_);
return v_res_34_;
}
}
lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WF(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_Int(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Omega_Int(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Basic(uint8_t builtin);
lean_object* initialize_Init_WF(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Omega_Int(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Omega_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Omega_Int(builtin);
}
#ifdef __cplusplus
}
#endif
