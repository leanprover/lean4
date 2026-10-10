// Lean compiler output
// Module: Init.Data.Subtype.Order
// Imports: public import Init.Data.Order.Classes import Init.Data.Order.Lemmas import Init.Ext
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
LEAN_EXPORT lean_object* l_Subtype_instLE___redArg();
LEAN_EXPORT lean_object* l_Subtype_instLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instLT___redArg();
LEAN_EXPORT lean_object* l_Subtype_instLT___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instTransLE___redArg();
LEAN_EXPORT lean_object* l_Subtype_instTransLE___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instTransLE(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subtype_instLE___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Subtype_instLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Subtype_instLE___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Subtype_instLE___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Subtype_instLE___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instLE(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_P_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
lean_object* l_Subtype_instLT___redArg(){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
LEAN_EXPORT void l_Subtype_instLT___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_12_;
v_res_12_ = l_Subtype_instLT___redArg();
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Subtype_instLT___redArg___boxed(lean_object* v___dummy_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Subtype_instLT___redArg();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instLT(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_P_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_box(0);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg___lam__0(lean_object* v_inst_19_, lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_apply_2(v_inst_19_, v_a_20_, v_b_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg(lean_object* v_inst_23_){
_start:
{
lean_object* v___f_24_; 
v___f_24_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_24_, 0, v_inst_23_);
return v___f_24_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_, lean_object* v_P_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_29_, 0, v_inst_26_);
return v___f_29_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMax___redArg(lean_object* v_inst_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_31_, 0, v_inst_30_);
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMax(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_P_35_){
_start:
{
lean_object* v___f_36_; 
v___f_36_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_36_, 0, v_inst_33_);
return v___f_36_;
}
}
lean_object* l_Subtype_instTransLE___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_box(0);
return v___x_38_;
}
}
LEAN_EXPORT void l_Subtype_instTransLE___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_39_;
v_res_39_ = l_Subtype_instTransLE___redArg();
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Subtype_instTransLE___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Subtype_instTransLE___redArg();
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instTransLE(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_i_44_, lean_object* v_P_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Subtype_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Subtype_Order(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Subtype_Order(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Subtype_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Subtype_Order(builtin);
}
#ifdef __cplusplus
}
#endif
