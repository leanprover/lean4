// Lean compiler output
// Module: Init.Data.List.ToArrayImpl
// Imports: public import Init.Prelude import Init.Data.List.Basic
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
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toArrayAux___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toArrayAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toArrayImpl___redArg(lean_object*);
LEAN_EXPORT lean_object* lean_list_to_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toArrayAux___redArg(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
return v_x_2_;
}
else
{
lean_object* v_head_3_; lean_object* v_tail_4_; lean_object* v___x_5_; 
v_head_3_ = lean_ctor_get(v_x_1_, 0);
lean_inc(v_head_3_);
v_tail_4_ = lean_ctor_get(v_x_1_, 1);
lean_inc(v_tail_4_);
lean_dec_ref(v_x_1_);
v___x_5_ = lean_array_push(v_x_2_, v_head_3_);
v_x_1_ = v_tail_4_;
v_x_2_ = v___x_5_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toArrayAux(lean_object* v_00_u03b1_7_, lean_object* v_x_8_, lean_object* v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_List_toArrayAux___redArg(v_x_8_, v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_List_toArrayImpl___redArg(lean_object* v_xs_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = l_List_lengthTR___redArg(v_xs_11_);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
lean_dec(v___x_12_);
v___x_14_ = l_List_toArrayAux___redArg(v_xs_11_, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lean_list_to_array(lean_object* v_00_u03b1_15_, lean_object* v_xs_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = l_List_lengthTR___redArg(v_xs_16_);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
lean_dec(v___x_17_);
v___x_19_ = l_List_toArrayAux___redArg(v_xs_16_, v___x_18_);
return v___x_19_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_ToArrayImpl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_ToArrayImpl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_ToArrayImpl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_ToArrayImpl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_ToArrayImpl(builtin);
}
#ifdef __cplusplus
}
#endif
