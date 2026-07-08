// Lean compiler output
// Module: Std.Data.Iterators.Producers.Vector
// Imports: public import Init.Data.Vector.Basic public import Std.Data.Iterators.Producers.Array
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
LEAN_EXPORT lean_object* l_Vector_iterFromIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Vector_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iter___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_iterFromIdx___redArg(lean_object* v_xs_1_, lean_object* v_pos_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_xs_1_);
lean_ctor_set(v___x_3_, 1, v_pos_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterFromIdx(lean_object* v_n_4_, lean_object* v_00_u03b1_5_, lean_object* v_xs_6_, lean_object* v_pos_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v_xs_6_);
lean_ctor_set(v___x_8_, 1, v_pos_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Vector_iterFromIdx___boxed(lean_object* v_n_9_, lean_object* v_00_u03b1_10_, lean_object* v_xs_11_, lean_object* v_pos_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Vector_iterFromIdx(v_n_9_, v_00_u03b1_10_, v_xs_11_, v_pos_12_);
lean_dec(v_n_9_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Vector_iter___redArg(lean_object* v_xs_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v_xs_14_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Vector_iter(lean_object* v_n_17_, lean_object* v_00_u03b1_18_, lean_object* v_xs_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_xs_19_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Vector_iter___boxed(lean_object* v_n_22_, lean_object* v_00_u03b1_23_, lean_object* v_xs_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Vector_iter(v_n_22_, v_00_u03b1_23_, v_xs_24_);
lean_dec(v_n_22_);
return v_res_25_;
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Vector(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Vector(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Vector(builtin);
}
#ifdef __cplusplus
}
#endif
