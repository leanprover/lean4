// Lean compiler output
// Module: Init.Data.Nat.Power2.Basic
// Imports: public import Init.Grind.Tactics import Init.Data.Nat.Linear import Init.NotationExtra import Init.WFTactics
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Nat_nextPowerOfTwo___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(lean_object* v_n_1_, lean_object* v_power_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_lt(v_power_2_, v_n_1_);
if (v___x_3_ == 0)
{
return v_power_2_;
}
else
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_mul(v_power_2_, v___x_4_);
lean_dec(v_power_2_);
v_power_2_ = v___x_5_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg___boxed(lean_object* v_n_7_, lean_object* v_power_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(v_n_7_, v_power_8_);
lean_dec(v_n_7_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go(lean_object* v_n_10_, lean_object* v_power_11_, lean_object* v_h_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(v_n_10_, v_power_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___boxed(lean_object* v_n_14_, lean_object* v_power_15_, lean_object* v_h_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go(v_n_14_, v_power_15_, v_h_16_);
lean_dec(v_n_14_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Nat_nextPowerOfTwo(lean_object* v_n_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(v_n_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Nat_nextPowerOfTwo___boxed(lean_object* v_n_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Nat_nextPowerOfTwo(v_n_21_);
lean_dec(v_n_21_);
return v_res_22_;
}
}
lean_object* runtime_initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_NotationExtra(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Power2_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Tactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Nat_Power2_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Nat_Power2_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
