// Lean compiler output
// Module: Std.Http.Server.Handler
// Imports: public import Std.Async public import Std.Http.Data public import Std.Async.ContextAsync
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
extern lean_object* l_Std_Http_Body_instAny;
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_instHandlerStatelessHandler___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_instHandlerStatelessHandler___closed__0 = (const lean_object*)&l_Std_Http_Server_instHandlerStatelessHandler___closed__0_value;
static const lean_closure_object l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_instHandlerStatelessHandler___closed__1 = (const lean_object*)&l_Std_Http_Server_instHandlerStatelessHandler___closed__1_value;
static const lean_closure_object l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_instHandlerStatelessHandler___closed__2 = (const lean_object*)&l_Std_Http_Server_instHandlerStatelessHandler___closed__2_value;
static lean_once_cell_t l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Server_instHandlerStatelessHandler___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler;
static const lean_ctor_object l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_Handler_ofFn___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Server_Handler_ofFn___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Server_Handler_ofFn___lam__1___closed__0 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value;
static const lean_ctor_object l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__1___closed__0_value)}};
static const lean_object* l_Std_Http_Server_Handler_ofFn___lam__1___closed__1 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Server_Handler_ofFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_Handler_ofFn___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_Handler_ofFn___closed__0 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___closed__0_value;
static const lean_closure_object l_Std_Http_Server_Handler_ofFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Server_Handler_ofFn___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Server_Handler_ofFn___closed__1 = (const lean_object*)&l_Std_Http_Server_Handler_ofFn___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFns(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withFailure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withContinue(lean_object*, lean_object*);
lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0(lean_object* v_self_1_, lean_object* v_request_2_, lean_object* v___y_3_){
_start:
{
lean_object* v_onRequest_5_; lean_object* v___x_6_; 
v_onRequest_5_ = lean_ctor_get(v_self_1_, 0);
lean_inc_ref(v_onRequest_5_);
lean_dec_ref(v_self_1_);
lean_inc_ref(v___y_3_);
v___x_6_ = lean_apply_3(v_onRequest_5_, v_request_2_, v___y_3_, lean_box(0));
return v___x_6_;
}
}
LEAN_EXPORT void l_Std_Http_Server_instHandlerStatelessHandler___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1_ = stack[0].m_obj;
lean_object* v_request_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__0(v_self_1_, v_request_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed(lean_object* v_self_8_, lean_object* v_request_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__0(v_self_8_, v_request_9_, v___y_10_);
lean_dec_ref(v___y_10_);
return v_res_12_;
}
}
lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1(lean_object* v_self_13_, lean_object* v_error_14_){
_start:
{
lean_object* v_onFailure_16_; lean_object* v___x_17_; 
v_onFailure_16_ = lean_ctor_get(v_self_13_, 1);
lean_inc_ref(v_onFailure_16_);
lean_dec_ref(v_self_13_);
v___x_17_ = lean_apply_2(v_onFailure_16_, v_error_14_, lean_box(0));
return v___x_17_;
}
}
LEAN_EXPORT void l_Std_Http_Server_instHandlerStatelessHandler___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_13_ = stack[0].m_obj;
lean_object* v_error_14_ = stack[1].m_obj;
lean_object* v_res_18_;
v_res_18_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__1(v_self_13_, v_error_14_);
stack->m_obj
 = v_res_18_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed(lean_object* v_self_19_, lean_object* v_error_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__1(v_self_19_, v_error_20_);
return v_res_22_;
}
}
lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2(lean_object* v_self_23_, lean_object* v_request_24_){
_start:
{
lean_object* v_onContinue_26_; lean_object* v___x_27_; 
v_onContinue_26_ = lean_ctor_get(v_self_23_, 2);
lean_inc_ref(v_onContinue_26_);
lean_dec_ref(v_self_23_);
v___x_27_ = lean_apply_2(v_onContinue_26_, v_request_24_, lean_box(0));
return v___x_27_;
}
}
LEAN_EXPORT void l_Std_Http_Server_instHandlerStatelessHandler___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_23_ = stack[0].m_obj;
lean_object* v_request_24_ = stack[1].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__2(v_self_23_, v_request_24_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed(lean_object* v_self_29_, lean_object* v_request_30_, lean_object* v___y_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__2(v_self_29_, v_request_30_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3(void){
_start:
{
lean_object* v___f_36_; lean_object* v___f_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___f_36_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__2));
v___f_37_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__1));
v___f_38_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__0));
v___x_39_ = l_Std_Http_Body_instAny;
v___x_40_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___f_38_);
lean_ctor_set(v___x_40_, 2, v___f_37_);
lean_ctor_set(v___x_40_, 3, v___f_36_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_Http_Server_instHandlerStatelessHandler(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Std_Http_Server_instHandlerStatelessHandler___closed__3, &l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once, _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3);
return v___x_41_;
}
}
lean_object* l_Std_Http_Server_Handler_ofFn___lam__0(lean_object* v_x_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___lam__0___closed__1));
return v___x_48_;
}
}
LEAN_EXPORT void l_Std_Http_Server_Handler_ofFn___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_46_ = stack[0].m_obj;
lean_object* v_res_49_;
v_res_49_ = l_Std_Http_Server_Handler_ofFn___lam__0(v_x_46_);
stack->m_obj
 = v_res_49_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__0___boxed(lean_object* v_x_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Http_Server_Handler_ofFn___lam__0(v_x_50_);
lean_dec(v_x_50_);
return v_res_52_;
}
}
lean_object* l_Std_Http_Server_Handler_ofFn___lam__1(lean_object* v_x_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___lam__1___closed__1));
return v___x_60_;
}
}
LEAN_EXPORT void l_Std_Http_Server_Handler_ofFn___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_58_ = stack[0].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Std_Http_Server_Handler_ofFn___lam__1(v_x_58_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__1___boxed(lean_object* v_x_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Http_Server_Handler_ofFn___lam__1(v_x_62_);
lean_dec_ref(v_x_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn(lean_object* v_f_67_){
_start:
{
lean_object* v___f_68_; lean_object* v___f_69_; lean_object* v___x_70_; 
v___f_68_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___closed__0));
v___f_69_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___closed__1));
v___x_70_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_70_, 0, v_f_67_);
lean_ctor_set(v___x_70_, 1, v___f_68_);
lean_ctor_set(v___x_70_, 2, v___f_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFns(lean_object* v_onRequest_71_, lean_object* v_onFailure_72_, lean_object* v_onContinue_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_74_, 0, v_onRequest_71_);
lean_ctor_set(v___x_74_, 1, v_onFailure_72_);
lean_ctor_set(v___x_74_, 2, v_onContinue_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withFailure(lean_object* v_handler_75_, lean_object* v_onFailure_76_){
_start:
{
lean_object* v_onRequest_77_; lean_object* v_onContinue_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
v_onRequest_77_ = lean_ctor_get(v_handler_75_, 0);
v_onContinue_78_ = lean_ctor_get(v_handler_75_, 2);
v_isSharedCheck_85_ = !lean_is_exclusive(v_handler_75_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_handler_75_, 1);
lean_dec(v_unused_86_);
v___x_80_ = v_handler_75_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_onContinue_78_);
lean_inc(v_onRequest_77_);
lean_dec(v_handler_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v_onFailure_76_);
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_onRequest_77_);
lean_ctor_set(v_reuseFailAlloc_84_, 1, v_onFailure_76_);
lean_ctor_set(v_reuseFailAlloc_84_, 2, v_onContinue_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withContinue(lean_object* v_handler_87_, lean_object* v_onContinue_88_){
_start:
{
lean_object* v_onRequest_89_; lean_object* v_onFailure_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_97_; 
v_onRequest_89_ = lean_ctor_get(v_handler_87_, 0);
v_onFailure_90_ = lean_ctor_get(v_handler_87_, 1);
v_isSharedCheck_97_ = !lean_is_exclusive(v_handler_87_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v_handler_87_, 2);
lean_dec(v_unused_98_);
v___x_92_ = v_handler_87_;
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_onFailure_90_);
lean_inc(v_onRequest_89_);
lean_dec(v_handler_87_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_97_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v_onContinue_88_);
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_onRequest_89_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_onFailure_90_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_onContinue_88_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_Server_instHandlerStatelessHandler = _init_l_Std_Http_Server_instHandlerStatelessHandler();
lean_mark_persistent(l_Std_Http_Server_instHandlerStatelessHandler);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Server_Handler(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Async(uint8_t builtin);
lean_object* initialize_Std_Http_Data(uint8_t builtin);
lean_object* initialize_Std_Async_ContextAsync(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Server_Handler(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Server_Handler(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Server_Handler(builtin);
}
#ifdef __cplusplus
}
#endif
