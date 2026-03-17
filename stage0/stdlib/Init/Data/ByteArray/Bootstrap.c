// Lean compiler output
// Module: Init.Data.ByteArray.Bootstrap
// Imports: public import Init.Data.List.Basic
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
lean_object* lean_byte_array_data(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_append(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_3_ = lean_byte_array_data(v_a_1_);
v___x_4_ = lean_array_to_list(v___x_3_);
v___x_5_ = lean_byte_array_data(v_b_2_);
v___x_6_ = lean_array_to_list(v___x_5_);
v___x_7_ = l_List_appendTR___redArg(v___x_4_, v___x_6_);
v___x_8_ = lean_array_mk(v___x_7_);
v___x_9_ = lean_byte_array_mk(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter___redArg(lean_object* v_x_10_, lean_object* v_x_11_, lean_object* v_h__1_12_, lean_object* v_h__2_13_){
_start:
{
if (lean_obj_tag(v_x_10_) == 0)
{
lean_object* v___x_14_; 
lean_dec(v_h__2_13_);
v___x_14_ = lean_apply_1(v_h__1_12_, v_x_11_);
return v___x_14_;
}
else
{
lean_object* v_head_15_; lean_object* v_tail_16_; lean_object* v___x_17_; 
lean_dec(v_h__1_12_);
v_head_15_ = lean_ctor_get(v_x_10_, 0);
lean_inc(v_head_15_);
v_tail_16_ = lean_ctor_get(v_x_10_, 1);
lean_inc(v_tail_16_);
lean_dec_ref(v_x_10_);
v___x_17_ = lean_apply_3(v_h__2_13_, v_head_15_, v_tail_16_, v_x_11_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter(lean_object* v_motive_18_, lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_h__1_21_, lean_object* v_h__2_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l___private_Init_Data_ByteArray_Bootstrap_0__List_toByteArray_match__1_splitter___redArg(v_x_19_, v_x_20_, v_h__1_21_, v_h__2_22_);
return v___x_23_;
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ByteArray_Bootstrap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ByteArray_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ByteArray_Bootstrap(builtin);
}
#ifdef __cplusplus
}
#endif
