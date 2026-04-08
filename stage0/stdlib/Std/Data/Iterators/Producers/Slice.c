// Lean compiler output
// Module: Std.Data.Iterators.Producers.Slice
// Imports: public import Init.Data.Slice.Operations
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
LEAN_EXPORT lean_object* l_Std_Slice_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Slice_iter___redArg(lean_object* v_inst_1_, lean_object* v_s_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_inst_1_, v_s_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_Slice_iter(lean_object* v_00_u03b3_4_, lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_inst_7_, lean_object* v_s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_inst_7_, v_s_8_);
return v___x_9_;
}
}
lean_object* runtime_initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice_Operations(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice_Operations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
