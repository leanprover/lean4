// Lean compiler output
// Module: Init.Data.Nat.Sqrt.Basic
// Imports: public import Init.Prelude public import Init.Data.Nat.Log2 public import Init.Data.Nat.Bitwise.Basic public import Init.WFTactics
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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_sqrt_iter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_sqrt_iter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_sqrt(lean_object*);
LEAN_EXPORT lean_object* l_Nat_sqrt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_sqrt_iter(lean_object* v_n_1_, lean_object* v_guess_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_next_6_; uint8_t v___x_7_; 
v___x_3_ = lean_nat_div(v_n_1_, v_guess_2_);
v___x_4_ = lean_nat_add(v_guess_2_, v___x_3_);
lean_dec(v___x_3_);
v___x_5_ = lean_unsigned_to_nat(1u);
v_next_6_ = lean_nat_shiftr(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = lean_nat_dec_lt(v_next_6_, v_guess_2_);
if (v___x_7_ == 0)
{
lean_dec(v_next_6_);
return v_guess_2_;
}
else
{
lean_dec(v_guess_2_);
v_guess_2_ = v_next_6_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Nat_sqrt_iter___boxed(lean_object* v_n_9_, lean_object* v_guess_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Nat_sqrt_iter(v_n_9_, v_guess_10_);
lean_dec(v_n_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Nat_sqrt(lean_object* v_n_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = lean_nat_dec_le(v_n_12_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_15_ = lean_nat_log2(v_n_12_);
v___x_16_ = lean_nat_shiftr(v___x_15_, v___x_13_);
lean_dec(v___x_15_);
v___x_17_ = lean_nat_add(v___x_16_, v___x_13_);
lean_dec(v___x_16_);
v___x_18_ = lean_nat_shiftl(v___x_13_, v___x_17_);
lean_dec(v___x_17_);
v___x_19_ = l_Nat_sqrt_iter(v_n_12_, v___x_18_);
return v___x_19_;
}
else
{
lean_inc(v_n_12_);
return v_n_12_;
}
}
}
LEAN_EXPORT lean_object* l_Nat_sqrt___boxed(lean_object* v_n_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Nat_sqrt(v_n_20_);
lean_dec(v_n_20_);
return v_res_21_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Sqrt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Sqrt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Sqrt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Sqrt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Sqrt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Sqrt_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
