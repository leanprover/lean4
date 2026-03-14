// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Vector
// Imports: public import Init.Data.Vector.Basic public import Std.Data.Iterators.Producers.Monadic.Array
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
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM___redArg(lean_object* v_xs_1_, lean_object* v_pos_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_xs_1_);
lean_ctor_set(v___x_3_, 1, v_pos_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM(lean_object* v_00_u03b1_4_, lean_object* v_n_5_, lean_object* v_xs_6_, lean_object* v_m_7_, lean_object* v_pos_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v_xs_6_);
lean_ctor_set(v___x_10_, 1, v_pos_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterFromIdxM___boxed(lean_object* v_00_u03b1_11_, lean_object* v_n_12_, lean_object* v_xs_13_, lean_object* v_m_14_, lean_object* v_pos_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Vector_iterFromIdxM(v_00_u03b1_11_, v_n_12_, v_xs_13_, v_m_14_, v_pos_15_, v_inst_16_);
lean_dec(v_inst_16_);
lean_dec(v_n_12_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterM___redArg(lean_object* v_xs_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v_xs_18_);
lean_ctor_set(v___x_20_, 1, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterM(lean_object* v_00_u03b1_21_, lean_object* v_n_22_, lean_object* v_xs_23_, lean_object* v_m_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_27_, 0, v_xs_23_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterM___boxed(lean_object* v_00_u03b1_28_, lean_object* v_n_29_, lean_object* v_xs_30_, lean_object* v_m_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Vector_iterM(v_00_u03b1_28_, v_n_29_, v_xs_30_, v_m_31_, v_inst_32_);
lean_dec(v_inst_32_);
lean_dec(v_n_29_);
return v_res_33_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Monadic_Vector(builtin);
}
#ifdef __cplusplus
}
#endif
