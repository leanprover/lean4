// Lean compiler output
// Module: Init.System.Promise
// Imports: public import Init.System.IO
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
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_PromisePointed;
lean_object* lean_io_promise_new();
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_option_get_or_block(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object*);
static const lean_closure_object l_IO_Promise_result_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_IO_Promise_result_x21___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_IO_Promise_result_x21___redArg___closed__0 = (const lean_object*)&l_IO_Promise_result_x21___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_Promise_isResolved(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Init_System_Promise_0__IO_PromisePointed(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(0);
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object* v_00_u03b1_5_, lean_object* v_inst_00___x40_Init_System_Promise_64347732____hygCtx___hyg_6_, lean_object* v_a_00___x40___internal___hyg_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lean_io_promise_new();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object* v_00_u03b1_13_, lean_object* v_value_14_, lean_object* v_promise_15_, lean_object* v_a_00___x40___internal___hyg_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lean_io_promise_resolve(v_value_14_, v_promise_15_);
lean_dec(v_promise_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object* v_00_u03b1_20_, lean_object* v_promise_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lean_io_promise_result_opt(v_promise_21_);
lean_dec(v_promise_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_00___x40_Init_System_Promise_1729115947____hygCtx___hyg_27_, lean_object* v_a_00___x40___internal___hyg_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lean_option_get_or_block(v_a_00___x40___internal___hyg_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object* v___y_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lean_option_get_or_block(v___y_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg(lean_object* v_promise_33_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; lean_object* v___x_38_; 
v___f_34_ = ((lean_object*)(l_IO_Promise_result_x21___redArg___closed__0));
v___x_35_ = lean_io_promise_result_opt(v_promise_33_);
v___x_36_ = lean_unsigned_to_nat(0u);
v___x_37_ = 1;
v___x_38_ = lean_task_map(v___f_34_, v___x_35_, v___x_36_, v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___boxed(lean_object* v_promise_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_IO_Promise_result_x21___redArg(v_promise_39_);
lean_dec(v_promise_39_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object* v_00_u03b1_41_, lean_object* v_promise_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_IO_Promise_result_x21___redArg(v_promise_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___boxed(lean_object* v_00_u03b1_44_, lean_object* v_promise_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_IO_Promise_result_x21(v_00_u03b1_44_, v_promise_45_);
lean_dec(v_promise_45_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t l_IO_Promise_isResolved___redArg(lean_object* v_promise_47_){
_start:
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = lean_io_promise_result_opt(v_promise_47_);
v___x_50_ = lean_io_get_task_state(v___x_49_);
lean_dec_ref(v___x_49_);
if (v___x_50_ == 2)
{
uint8_t v___x_51_; 
v___x_51_ = 1;
return v___x_51_;
}
else
{
uint8_t v___x_52_; 
v___x_52_ = 0;
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___redArg___boxed(lean_object* v_promise_53_, lean_object* v_a_54_){
_start:
{
uint8_t v_res_55_; lean_object* v_r_56_; 
v_res_55_ = l_IO_Promise_isResolved___redArg(v_promise_53_);
lean_dec(v_promise_53_);
v_r_56_ = lean_box(v_res_55_);
return v_r_56_;
}
}
LEAN_EXPORT uint8_t l_IO_Promise_isResolved(lean_object* v_00_u03b1_57_, lean_object* v_promise_58_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = l_IO_Promise_isResolved___redArg(v_promise_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___boxed(lean_object* v_00_u03b1_61_, lean_object* v_promise_62_, lean_object* v_a_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_IO_Promise_isResolved(v_00_u03b1_61_, v_promise_62_);
lean_dec(v_promise_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_System_Promise_0__IO_PromisePointed = _init_l___private_Init_System_Promise_0__IO_PromisePointed();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_Promise(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Promise(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_Promise(builtin);
}
#ifdef __cplusplus
}
#endif
