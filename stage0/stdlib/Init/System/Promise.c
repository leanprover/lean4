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
LEAN_EXPORT void l_IO_Promise_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5_;
v_res_5_ = lean_io_promise_new();
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_IO_Promise_new___boxed(lean_object* v_00_u03b1_6_, lean_object* v_inst_00___x40_Init_System_Promise_64347732____hygCtx___hyg_7_, lean_object* v_a_00___x40___internal___hyg_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lean_io_promise_new();
return v_res_9_;
}
}
LEAN_EXPORT void l_IO_Promise_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_11_ = stack[1].m_obj;
lean_object* v_promise_12_ = stack[2].m_obj;
lean_object* v_res_14_;
v_res_14_ = lean_io_promise_resolve(v_value_11_, v_promise_12_);
stack->m_obj
 = v_res_14_;
}
LEAN_EXPORT lean_object* l_IO_Promise_resolve___boxed(lean_object* v_00_u03b1_15_, lean_object* v_value_16_, lean_object* v_promise_17_, lean_object* v_a_00___x40___internal___hyg_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = lean_io_promise_resolve(v_value_16_, v_promise_17_);
lean_dec(v_promise_17_);
return v_res_19_;
}
}
LEAN_EXPORT void l_IO_Promise_result_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_21_ = stack[1].m_obj;
lean_object* v_res_22_;
v_res_22_ = lean_io_promise_result_opt(v_promise_21_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x3f___boxed(lean_object* v_00_u03b1_23_, lean_object* v_promise_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lean_io_promise_result_opt(v_promise_24_);
lean_dec(v_promise_24_);
return v_res_25_;
}
}
LEAN_EXPORT void l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_00___x40___internal___hyg_28_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = lean_option_get_or_block(v_a_00___x40___internal___hyg_28_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l___private_Init_System_Promise_0__IO_Option_getOrBlock_x21___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_00___x40_Init_System_Promise_1729115947____hygCtx___hyg_31_, lean_object* v_a_00___x40___internal___hyg_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = lean_option_get_or_block(v_a_00___x40___internal___hyg_32_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___lam__0(lean_object* v___y_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = lean_option_get_or_block(v___y_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg(lean_object* v_promise_37_){
_start:
{
lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; 
v___f_38_ = ((lean_object*)(l_IO_Promise_result_x21___redArg___closed__0));
v___x_39_ = lean_io_promise_result_opt(v_promise_37_);
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = 1;
v___x_42_ = lean_task_map(v___f_38_, v___x_39_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___redArg___boxed(lean_object* v_promise_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_IO_Promise_result_x21___redArg(v_promise_43_);
lean_dec(v_promise_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21(lean_object* v_00_u03b1_45_, lean_object* v_promise_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_IO_Promise_result_x21___redArg(v_promise_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_IO_Promise_result_x21___boxed(lean_object* v_00_u03b1_48_, lean_object* v_promise_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_IO_Promise_result_x21(v_00_u03b1_48_, v_promise_49_);
lean_dec(v_promise_49_);
return v_res_50_;
}
}
uint8_t l_IO_Promise_isResolved___redArg(lean_object* v_promise_51_){
_start:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_io_promise_result_opt(v_promise_51_);
v___x_54_ = lean_io_get_task_state(v___x_53_);
lean_dec_ref(v___x_53_);
if (v___x_54_ == 2)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
LEAN_EXPORT void l_IO_Promise_isResolved___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_51_ = stack[0].m_obj;
uint8_t v_res_57_;
v_res_57_ = l_IO_Promise_isResolved___redArg(v_promise_51_);
stack->m_num = v_res_57_;
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___redArg___boxed(lean_object* v_promise_58_, lean_object* v_a_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_IO_Promise_isResolved___redArg(v_promise_58_);
lean_dec(v_promise_58_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
uint8_t l_IO_Promise_isResolved(lean_object* v_00_u03b1_62_, lean_object* v_promise_63_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l_IO_Promise_isResolved___redArg(v_promise_63_);
return v___x_65_;
}
}
LEAN_EXPORT void l_IO_Promise_isResolved_0interp(lean_interpreter_value* stack)
{
lean_object* v_promise_63_ = stack[1].m_obj;
uint8_t v_res_66_;
v_res_66_ = l_IO_Promise_isResolved(lean_box(0), v_promise_63_);
stack->m_num = v_res_66_;
}
LEAN_EXPORT lean_object* l_IO_Promise_isResolved___boxed(lean_object* v_00_u03b1_67_, lean_object* v_promise_68_, lean_object* v_a_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_IO_Promise_isResolved(v_00_u03b1_67_, v_promise_68_);
lean_dec(v_promise_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
