// Lean compiler output
// Module: Init.Data.Vector.Monadic
// Imports: import all Init.Data.Vector.Basic public import Init.Data.Vector.Attach import Init.Data.Array.Monadic
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
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (lean_obj_tag(v_b_1_) == 0)
{
lean_object* v_a_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v_a_4_ = lean_ctor_get(v_b_1_, 0);
lean_inc(v_a_4_);
lean_dec_ref(v_b_1_);
v___x_5_ = lean_apply_1(v_h__2_3_, v_a_4_);
return v___x_5_;
}
else
{
lean_object* v_a_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v_a_6_ = lean_ctor_get(v_b_1_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v_b_1_);
v___x_7_ = lean_apply_1(v_h__1_2_, v_a_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Array_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_8_, lean_object* v_motive_9_, lean_object* v_b_10_, lean_object* v_h__1_11_, lean_object* v_h__2_12_){
_start:
{
if (lean_obj_tag(v_b_10_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
lean_dec(v_h__1_11_);
v_a_13_ = lean_ctor_get(v_b_10_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v_b_10_);
v___x_14_ = lean_apply_1(v_h__2_12_, v_a_13_);
return v___x_14_;
}
else
{
lean_object* v_a_15_; lean_object* v___x_16_; 
lean_dec(v_h__2_12_);
v_a_15_ = lean_ctor_get(v_b_10_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v_b_10_);
v___x_16_ = lean_apply_1(v_h__1_11_, v_a_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter___redArg(lean_object* v_b_17_, lean_object* v_h__1_18_, lean_object* v_h__2_19_){
_start:
{
if (lean_obj_tag(v_b_17_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_21_; 
lean_dec(v_h__1_18_);
v_a_20_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_a_20_);
lean_dec_ref(v_b_17_);
v___x_21_ = lean_apply_1(v_h__2_19_, v_a_20_);
return v___x_21_;
}
else
{
lean_object* v_a_22_; lean_object* v___x_23_; 
lean_dec(v_h__2_19_);
v_a_22_ = lean_ctor_get(v_b_17_, 0);
lean_inc(v_a_22_);
lean_dec_ref(v_b_17_);
v___x_23_ = lean_apply_1(v_h__1_18_, v_a_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Monadic_0__Vector_forIn_x27__eq__foldlM_match__1_splitter(lean_object* v_00_u03b2_24_, lean_object* v_motive_25_, lean_object* v_b_26_, lean_object* v_h__1_27_, lean_object* v_h__2_28_){
_start:
{
if (lean_obj_tag(v_b_26_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
lean_dec(v_h__1_27_);
v_a_29_ = lean_ctor_get(v_b_26_, 0);
lean_inc(v_a_29_);
lean_dec_ref(v_b_26_);
v___x_30_ = lean_apply_1(v_h__2_28_, v_a_29_);
return v___x_30_;
}
else
{
lean_object* v_a_31_; lean_object* v___x_32_; 
lean_dec(v_h__2_28_);
v_a_31_ = lean_ctor_get(v_b_26_, 0);
lean_inc(v_a_31_);
lean_dec_ref(v_b_26_);
v___x_32_ = lean_apply_1(v_h__1_27_, v_a_31_);
return v___x_32_;
}
}
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Monadic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Vector_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Vector_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Monadic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Vector_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Vector_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Vector_Monadic(builtin);
}
#ifdef __cplusplus
}
#endif
