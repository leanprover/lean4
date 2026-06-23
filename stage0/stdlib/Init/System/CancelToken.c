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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_CancelToken_new(){
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
LEAN_EXPORT lean_object* l_IO_CancelToken_new___boxed(lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_IO_CancelToken_new();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set(lean_object* v_tk_9_){
_start:
{
lean_object* v_promise_11_; lean_object* v_setRef_12_; lean_object* v___x_13_; lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v_promise_11_ = lean_ctor_get(v_tk_9_, 0);
v_setRef_12_ = lean_ctor_get(v_tk_9_, 1);
v___x_13_ = lean_box(0);
v___x_14_ = lean_io_promise_resolve(v___x_13_, v_promise_11_);
v___x_15_ = 1;
v___x_16_ = lean_box(v___x_15_);
v___x_17_ = lean_st_ref_set(v_setRef_12_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_set___boxed(lean_object* v_tk_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_IO_CancelToken_set(v_tk_18_);
lean_dec_ref(v_tk_18_);
return v_res_20_;
}
}
LEAN_EXPORT uint8_t l_IO_CancelToken_isSet(lean_object* v_tk_21_){
_start:
{
lean_object* v_setRef_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v_setRef_23_ = lean_ctor_get(v_tk_21_, 1);
v___x_24_ = lean_st_ref_get(v_setRef_23_);
v___x_25_ = lean_unbox(v___x_24_);
lean_dec(v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_isSet___boxed(lean_object* v_tk_26_, lean_object* v_a_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_IO_CancelToken_isSet(v_tk_26_);
lean_dec_ref(v_tk_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___lam__0(lean_object* v_action_30_, lean_object* v_x_31_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_apply_1(v_action_30_, lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___lam__0___boxed(lean_object* v_action_34_, lean_object* v_x_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_IO_CancelToken_onSet___lam__0(v_action_34_, v_x_35_);
lean_dec(v_x_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet(lean_object* v_tk_38_, lean_object* v_action_39_){
_start:
{
lean_object* v_promise_41_; lean_object* v___f_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; lean_object* v___x_46_; 
v_promise_41_ = lean_ctor_get(v_tk_38_, 0);
v___f_42_ = lean_alloc_closure((void*)(l_IO_CancelToken_onSet___lam__0___boxed), 3, 1);
lean_closure_set(v___f_42_, 0, v_action_39_);
v___x_43_ = lean_io_promise_result_opt(v_promise_41_);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = 1;
v___x_46_ = l_BaseIO_chainTask___redArg(v___x_43_, v___f_42_, v___x_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_IO_CancelToken_onSet___boxed(lean_object* v_tk_47_, lean_object* v_action_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_IO_CancelToken_onSet(v_tk_47_, v_action_48_);
lean_dec_ref(v_tk_47_);
return v_res_50_;
}
}
LEAN_EXPORT uint8_t lean_io_cancel_token_is_set(lean_object* v_tk_51_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = l_IO_CancelToken_isSet(v_tk_51_);
lean_dec_ref(v_tk_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_CancelToken_0__IO_CancelToken_isSetExport___boxed(lean_object* v_tk_54_, lean_object* v_a_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = lean_io_cancel_token_is_set(v_tk_54_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
lean_object* runtime_initialize_Init_System_Promise(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_System_CancelToken(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
