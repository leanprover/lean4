// Lean compiler output
// Module: Init.Data.Nat.Power2.Lemmas
// Imports: import all Init.Data.Nat.Power2.Basic public import Init.Data.Nat.Log2 public import Init.Data.Nat.Power2.Basic public import Init.PropLemmas import Init.ByCases import Init.Data.Int.Pow import Init.Data.Nat.Bitwise.Lemmas import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Nat_instDecidableIsPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Nat_instDecidableIsPowerOfTwo___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Nat_instDecidableIsPowerOfTwo(lean_object* v_n_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_nat_dec_eq(v_n_1_, v___x_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_n_1_, v___x_4_);
v___x_6_ = lean_nat_land(v_n_1_, v___x_5_);
lean_dec(v___x_5_);
v___x_7_ = lean_nat_dec_eq(v___x_6_, v___x_2_);
lean_dec(v___x_6_);
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_instDecidableIsPowerOfTwo___boxed(lean_object* v_n_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Nat_instDecidableIsPowerOfTwo(v_n_9_);
lean_dec(v_n_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Power2_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
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
res = runtime_initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Power2_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Power2_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
