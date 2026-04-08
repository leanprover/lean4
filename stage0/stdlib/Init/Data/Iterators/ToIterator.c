// Lean compiler output
// Module: Init.Data.Iterators.ToIterator
// Imports: public import Init.Data.Iterators.Basic
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
LEAN_EXPORT lean_object* l_Std_ToIterator_iterM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_iterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_iter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_of___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_of___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_of(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_ToIterator_iterM___redArg(lean_object* v_x_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_1(v_inst_2_, v_x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_iterM(lean_object* v_00_u03b3_4_, lean_object* v_m_5_, lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_x_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_apply_1(v_inst_9_, v_x_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_iter___redArg(lean_object* v_inst_11_, lean_object* v_x_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_apply_1(v_inst_11_, v_x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_iter(lean_object* v_00_u03b3_14_, lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_inst_17_, lean_object* v_x_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_apply_1(v_inst_17_, v_x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM___redArg___lam__0(lean_object* v_iterM_20_, lean_object* v_x_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_1(v_iterM_20_, v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM___redArg(lean_object* v_iterM_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(l_Std_ToIterator_ofM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_24_, 0, v_iterM_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_ofM(lean_object* v_00_u03b3_25_, lean_object* v_m_26_, lean_object* v_00_u03b2_27_, lean_object* v_00_u03b1_28_, lean_object* v_iterM_29_){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = lean_alloc_closure((void*)(l_Std_ToIterator_ofM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_30_, 0, v_iterM_29_);
return v___f_30_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_of___redArg___lam__0(lean_object* v_iter_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_1(v_iter_31_, v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_of___redArg(lean_object* v_iter_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = lean_alloc_closure((void*)(l_Std_ToIterator_of___redArg___lam__0), 2, 1);
lean_closure_set(v___f_35_, 0, v_iter_34_);
return v___f_35_;
}
}
LEAN_EXPORT lean_object* l_Std_ToIterator_of(lean_object* v_00_u03b3_36_, lean_object* v_00_u03b2_37_, lean_object* v_00_u03b1_38_, lean_object* v_iter_39_){
_start:
{
lean_object* v___f_40_; 
v___f_40_ = lean_alloc_closure((void*)(l_Std_ToIterator_of___redArg___lam__0), 2, 1);
lean_closure_set(v___f_40_, 0, v_iter_39_);
return v___f_40_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_ToIterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_ToIterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_ToIterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_ToIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_ToIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_ToIterator(builtin);
}
#ifdef __cplusplus
}
#endif
