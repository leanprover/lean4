// Lean compiler output
// Module: Std.Data.Iterators.Combinators.StepSize
// Imports: public import Std.Data.Iterators.Combinators.Monadic.StepSize
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_stepSize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___redArg(lean_object* v_it_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_unsigned_to_nat(1u);
v___x_5_ = lean_nat_sub(v_n_2_, v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6_, 0, v___x_3_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v_it_1_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___redArg___boxed(lean_object* v_it_7_, lean_object* v_n_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Std_Iter_stepSize___redArg(v_it_7_, v_n_8_);
lean_dec(v_n_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_stepSize(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_inst_12_, lean_object* v_inst_13_, lean_object* v_it_14_, lean_object* v_n_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_sub(v_n_15_, v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_16_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
lean_ctor_set(v___x_19_, 2, v_it_14_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_stepSize___boxed(lean_object* v_00_u03b1_20_, lean_object* v_00_u03b2_21_, lean_object* v_inst_22_, lean_object* v_inst_23_, lean_object* v_it_24_, lean_object* v_n_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Iter_stepSize(v_00_u03b1_20_, v_00_u03b2_21_, v_inst_22_, v_inst_23_, v_it_24_, v_n_25_);
lean_dec(v_n_25_);
lean_dec_ref(v_inst_23_);
lean_dec(v_inst_22_);
return v_res_26_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
}
#ifdef __cplusplus
}
#endif
