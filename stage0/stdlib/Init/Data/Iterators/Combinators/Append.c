// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Append
// Imports: public import Init.Data.Iterators.Combinators.Monadic.Append
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
LEAN_EXPORT lean_object* l_Std_Iter_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_append(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_append___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_append___redArg(lean_object* v_it_u2081_1_, lean_object* v_it_u2082_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_it_u2081_1_);
lean_ctor_set(v___x_3_, 1, v_it_u2082_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_append(lean_object* v_00_u03b1_u2081_4_, lean_object* v_00_u03b1_u2082_5_, lean_object* v_00_u03b2_6_, lean_object* v_inst_7_, lean_object* v_inst_8_, lean_object* v_it_u2081_9_, lean_object* v_it_u2082_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_it_u2081_9_);
lean_ctor_set(v___x_11_, 1, v_it_u2082_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_append___boxed(lean_object* v_00_u03b1_u2081_12_, lean_object* v_00_u03b1_u2082_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_it_u2081_17_, lean_object* v_it_u2082_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Iter_append(v_00_u03b1_u2081_12_, v_00_u03b1_u2082_13_, v_00_u03b2_14_, v_inst_15_, v_inst_16_, v_it_u2081_17_, v_it_u2082_18_);
lean_dec(v_inst_16_);
lean_dec(v_inst_15_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd___redArg(lean_object* v_it_u2082_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_it_u2082_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd(lean_object* v_00_u03b1_u2082_22_, lean_object* v_00_u03b2_23_, lean_object* v_inst_24_, lean_object* v_00_u03b1_u2081_25_, lean_object* v_it_u2082_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_27_, 0, v_it_u2082_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_Intermediate_appendSnd___boxed(lean_object* v_00_u03b1_u2082_28_, lean_object* v_00_u03b2_29_, lean_object* v_inst_30_, lean_object* v_00_u03b1_u2081_31_, lean_object* v_it_u2082_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Iter_Intermediate_appendSnd(v_00_u03b1_u2082_28_, v_00_u03b2_29_, v_inst_30_, v_00_u03b1_u2081_31_, v_it_u2082_32_);
lean_dec(v_inst_30_);
return v_res_33_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Append(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Append(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Monadic_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Append(builtin);
}
#ifdef __cplusplus
}
#endif
