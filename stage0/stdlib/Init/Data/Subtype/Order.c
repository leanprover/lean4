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
LEAN_EXPORT lean_object* l_Subtype_instLE(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instLT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMin(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instMax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instTransLE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subtype_instLE(lean_object* v_00_u03b1_1_, lean_object* v_inst_2_, lean_object* v_P_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(0);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instLT(lean_object* v_00_u03b1_5_, lean_object* v_inst_6_, lean_object* v_P_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg___lam__0(lean_object* v_inst_9_, lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_2(v_inst_9_, v_a_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin___redArg(lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_14_, 0, v_inst_13_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMin(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_P_18_){
_start:
{
lean_object* v___f_19_; 
v___f_19_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_19_, 0, v_inst_16_);
return v___f_19_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMax___redArg(lean_object* v_inst_20_){
_start:
{
lean_object* v___f_21_; 
v___f_21_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_21_, 0, v_inst_20_);
return v___f_21_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instMax(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_, lean_object* v_P_25_){
_start:
{
lean_object* v___f_26_; 
v___f_26_ = lean_alloc_closure((void*)(l_Subtype_instMin___redArg___lam__0), 3, 1);
lean_closure_set(v___f_26_, 0, v_inst_23_);
return v___f_26_;
}
}
LEAN_EXPORT lean_object* l_Subtype_instTransLE(lean_object* v_00_u03b1_27_, lean_object* v_inst_28_, lean_object* v_i_29_, lean_object* v_P_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_box(0);
return v___x_31_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Subtype_Order(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
