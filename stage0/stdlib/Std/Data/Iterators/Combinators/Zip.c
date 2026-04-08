// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Zip
// Imports: public import Std.Data.Iterators.Combinators.Monadic.Zip
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
LEAN_EXPORT lean_object* l_Std_Iter_zip___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_zip(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_zip___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_zip___redArg(lean_object* v_left_1_, lean_object* v_right_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_box(0);
v___x_4_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4_, 0, v_left_1_);
lean_ctor_set(v___x_4_, 1, v___x_3_);
lean_ctor_set(v___x_4_, 2, v_right_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_zip(lean_object* v_00_u03b1_u2081_5_, lean_object* v_00_u03b2_u2081_6_, lean_object* v_00_u03b1_u2082_7_, lean_object* v_00_u03b2_u2082_8_, lean_object* v_inst_9_, lean_object* v_inst_10_, lean_object* v_left_11_, lean_object* v_right_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_box(0);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v_left_11_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
lean_ctor_set(v___x_14_, 2, v_right_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_zip___boxed(lean_object* v_00_u03b1_u2081_15_, lean_object* v_00_u03b2_u2081_16_, lean_object* v_00_u03b1_u2082_17_, lean_object* v_00_u03b2_u2082_18_, lean_object* v_inst_19_, lean_object* v_inst_20_, lean_object* v_left_21_, lean_object* v_right_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Iter_zip(v_00_u03b1_u2081_15_, v_00_u03b2_u2081_16_, v_00_u03b1_u2082_17_, v_00_u03b2_u2082_18_, v_inst_19_, v_inst_20_, v_left_21_, v_right_22_);
lean_dec(v_inst_20_);
lean_dec(v_inst_19_);
return v_res_23_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Zip(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Combinators_Zip(builtin);
}
#ifdef __cplusplus
}
#endif
