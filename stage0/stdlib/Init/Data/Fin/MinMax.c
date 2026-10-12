// Lean compiler output
// Module: Init.Data.Fin.MinMax
// Imports: public import Init.Data.Fin.Basic import Init.Data.Order.Lemmas import Init.Data.Nat.Order import Init.Data.Nat.MinMax
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instMin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instMin___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instMin___redArg___closed__0 = (const lean_object*)&l_Fin_instMin___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instMin___redArg();
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMin(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMin___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Fin_instMax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Fin_instMax___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Fin_instMax___redArg___closed__0 = (const lean_object*)&l_Fin_instMax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Fin_instMax___redArg();
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMax(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___lam__0(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_nat_dec_le(v_a_1_, v_b_2_);
if (v___x_3_ == 0)
{
lean_inc(v_b_2_);
return v_b_2_;
}
else
{
lean_inc(v_a_1_);
return v_a_1_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___lam__0___boxed(lean_object* v_a_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Fin_instMin___redArg___lam__0(v_a_4_, v_b_5_);
lean_dec(v_b_5_);
lean_dec(v_a_4_);
return v_res_6_;
}
}
lean_object* l_Fin_instMin___redArg(){
_start:
{
lean_object* v___f_9_; 
v___f_9_ = ((lean_object*)(l_Fin_instMin___redArg___closed__0));
return v___f_9_;
}
}
LEAN_EXPORT void l_Fin_instMin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_10_;
v_res_10_ = l_Fin_instMin___redArg();
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Fin_instMin___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Fin_instMin___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMin(lean_object* v_n_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = ((lean_object*)(l_Fin_instMin___redArg___closed__0));
return v___f_14_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMin___boxed(lean_object* v_n_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Fin_instMin(v_n_15_);
lean_dec(v_n_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___lam__0(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_le(v_a_17_, v_b_18_);
if (v___x_19_ == 0)
{
lean_inc(v_a_17_);
return v_a_17_;
}
else
{
lean_inc(v_b_18_);
return v_b_18_;
}
}
}
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___lam__0___boxed(lean_object* v_a_20_, lean_object* v_b_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Fin_instMax___redArg___lam__0(v_a_20_, v_b_21_);
lean_dec(v_b_21_);
lean_dec(v_a_20_);
return v_res_22_;
}
}
lean_object* l_Fin_instMax___redArg(){
_start:
{
lean_object* v___f_25_; 
v___f_25_ = ((lean_object*)(l_Fin_instMax___redArg___closed__0));
return v___f_25_;
}
}
LEAN_EXPORT void l_Fin_instMax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_26_;
v_res_26_ = l_Fin_instMax___redArg();
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Fin_instMax___redArg___boxed(lean_object* v___dummy_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Fin_instMax___redArg();
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMax(lean_object* v_n_29_){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = ((lean_object*)(l_Fin_instMax___redArg___closed__0));
return v___f_30_;
}
}
LEAN_EXPORT lean_object* l_Fin_instMax___boxed(lean_object* v_n_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Fin_instMax(v_n_31_);
lean_dec(v_n_31_);
return v_res_32_;
}
}
lean_object* runtime_initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Fin_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Fin_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Fin_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_MinMax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Fin_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Fin_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Fin_MinMax(builtin);
}
#ifdef __cplusplus
}
#endif
