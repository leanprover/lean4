// Lean compiler output
// Module: Init.System.CancelToken
// Imports: public import Init.System.Promise
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
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_new();
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_CancelToken_0__IO_CancelToken_isSetExport___boxed(lean_object*, lean_object*);
lean_object* l_IO_CancelToken_new(){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_2_ = lean_io_promise_new();
v___x_3_ = 0;
v___x_4_ = lean_box(v___x_3_);
v___x_5_ = lean_st_mk_ref(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_2_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_IO_CancelToken_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_IO_CancelToken_new();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object* v_a_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_IO_CancelToken_new();
return v_res_9_;
}
}
lean_object* l_IO_CancelToken_set(lean_object* v_tk_10_){
_start:
{
lean_object* v_promise_12_; lean_object* v_setRef_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v_promise_12_ = lean_ctor_get(v_tk_10_, 0);
v_setRef_13_ = lean_ctor_get(v_tk_10_, 1);
v___x_14_ = lean_box(0);
v___x_15_ = lean_io_promise_resolve(v___x_14_, v_promise_12_);
v___x_16_ = 1;
v___x_17_ = lean_box(v___x_16_);
v___x_18_ = lean_st_ref_swap(v_setRef_13_, v___x_17_);
lean_dec(v___x_18_);
return v___x_14_;
}
}
LEAN_EXPORT void l_IO_CancelToken_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_10_ = stack[0].m_obj;
lean_object* v_res_19_;
v_res_19_ = l_IO_CancelToken_set(v_tk_10_);
stack->m_obj
 = v_res_19_;
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* v_tk_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_CancelToken_set(v_tk_20_);
lean_dec_ref(v_tk_20_);
return v_res_22_;
}
}
uint8_t l_IO_CancelToken_isSet(lean_object* v_tk_23_){
_start:
{
lean_object* v_setRef_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
v_setRef_25_ = lean_ctor_get(v_tk_23_, 1);
v___x_26_ = lean_st_ref_get(v_setRef_25_);
v___x_27_ = lean_unbox(v___x_26_);
lean_dec(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_IO_CancelToken_isSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_23_ = stack[0].m_obj;
uint8_t v_res_28_;
v_res_28_ = l_IO_CancelToken_isSet(v_tk_23_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* v_tk_29_, lean_object* v_a_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_IO_CancelToken_isSet(v_tk_29_);
lean_dec_ref(v_tk_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
lean_object* l_IO_CancelToken_onSet___lam__0(lean_object* v_action_33_, lean_object* v_x_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_apply_1(v_action_33_, lean_box(0));
return v___x_36_;
}
}
LEAN_EXPORT void l_IO_CancelToken_onSet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_action_33_ = stack[0].m_obj;
lean_object* v_x_34_ = stack[1].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_IO_CancelToken_onSet___lam__0(v_action_33_, v_x_34_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___lam__0___boxed(lean_object* v_action_38_, lean_object* v_x_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_IO_CancelToken_onSet___lam__0(v_action_38_, v_x_39_);
lean_dec(v_x_39_);
return v_res_41_;
}
}
lean_object* l_IO_CancelToken_onSet(lean_object* v_tk_42_, lean_object* v_action_43_){
_start:
{
lean_object* v_promise_45_; lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; 
v_promise_45_ = lean_ctor_get(v_tk_42_, 0);
v___f_46_ = lean_alloc_closure((void*)(l_IO_CancelToken_onSet___lam__0___boxed), 3, 1);
lean_closure_set(v___f_46_, 0, v_action_43_);
v___x_47_ = lean_io_promise_result_opt(v_promise_45_);
v___x_48_ = lean_unsigned_to_nat(0u);
v___x_49_ = 1;
v___x_50_ = l_BaseIO_chainTask___redArg(v___x_47_, v___f_46_, v___x_48_, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT void l_IO_CancelToken_onSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_42_ = stack[0].m_obj;
lean_object* v_action_43_ = stack[1].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_IO_CancelToken_onSet(v_tk_42_, v_action_43_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___boxed(lean_object* v_tk_52_, lean_object* v_action_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_IO_CancelToken_onSet(v_tk_52_, v_action_53_);
lean_dec_ref(v_tk_52_);
return v_res_55_;
}
}
uint8_t lean_io_cancel_token_is_set(lean_object* v_tk_56_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = l_IO_CancelToken_isSet(v_tk_56_);
lean_dec_ref(v_tk_56_);
return v___x_58_;
}
}
LEAN_EXPORT void lean_io_cancel_token_is_set_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_56_ = stack[0].m_obj;
uint8_t v_res_59_;
v_res_59_ = lean_io_cancel_token_is_set(v_tk_56_);
stack->m_num = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Init_System_CancelToken_0__IO_CancelToken_isSetExport___boxed(lean_object* v_tk_60_, lean_object* v_a_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = lean_io_cancel_token_is_set(v_tk_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_CancelToken(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_System_CancelToken(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Promise(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_CancelToken(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Promise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_CancelToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_System_CancelToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_System_CancelToken(builtin);
}
#ifdef __cplusplus
}
#endif
