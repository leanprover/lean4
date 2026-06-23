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
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0(lean_object* v_self_1_, lean_object* v_request_2_, lean_object* v___y_3_){
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
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__0___boxed(lean_object* v_self_7_, lean_object* v_request_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__0(v_self_7_, v_request_8_, v___y_9_);
lean_dec_ref(v___y_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1(lean_object* v_self_12_, lean_object* v_error_13_){
_start:
{
lean_object* v_onFailure_15_; lean_object* v___x_16_; 
v_onFailure_15_ = lean_ctor_get(v_self_12_, 1);
lean_inc_ref(v_onFailure_15_);
lean_dec_ref(v_self_12_);
v___x_16_ = lean_apply_2(v_onFailure_15_, v_error_13_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__1___boxed(lean_object* v_self_17_, lean_object* v_error_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__1(v_self_17_, v_error_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2(lean_object* v_self_21_, lean_object* v_request_22_){
_start:
{
lean_object* v_onContinue_24_; lean_object* v___x_25_; 
v_onContinue_24_ = lean_ctor_get(v_self_21_, 2);
lean_inc_ref(v_onContinue_24_);
lean_dec_ref(v_self_21_);
v___x_25_ = lean_apply_2(v_onContinue_24_, v_request_22_, lean_box(0));
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_instHandlerStatelessHandler___lam__2___boxed(lean_object* v_self_26_, lean_object* v_request_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Std_Http_Server_instHandlerStatelessHandler___lam__2(v_self_26_, v_request_27_);
return v_res_29_;
}
}
static lean_object* _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3(void){
_start:
{
lean_object* v___f_33_; lean_object* v___f_34_; lean_object* v___f_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___f_33_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__2));
v___f_34_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__1));
v___f_35_ = ((lean_object*)(l_Std_Http_Server_instHandlerStatelessHandler___closed__0));
v___x_36_ = l_Std_Http_Body_instAny;
v___x_37_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___f_35_);
lean_ctor_set(v___x_37_, 2, v___f_34_);
lean_ctor_set(v___x_37_, 3, v___f_33_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Http_Server_instHandlerStatelessHandler(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_Http_Server_instHandlerStatelessHandler___closed__3, &l_Std_Http_Server_instHandlerStatelessHandler___closed__3_once, _init_l_Std_Http_Server_instHandlerStatelessHandler___closed__3);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__0(lean_object* v_x_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___lam__0___closed__1));
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__0___boxed(lean_object* v_x_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Http_Server_Handler_ofFn___lam__0(v_x_46_);
lean_dec(v_x_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__1(lean_object* v_x_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___lam__1___closed__1));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn___lam__1___boxed(lean_object* v_x_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_Http_Server_Handler_ofFn___lam__1(v_x_57_);
lean_dec_ref(v_x_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFn(lean_object* v_f_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; 
v___f_63_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___closed__0));
v___f_64_ = ((lean_object*)(l_Std_Http_Server_Handler_ofFn___closed__1));
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v_f_62_);
lean_ctor_set(v___x_65_, 1, v___f_63_);
lean_ctor_set(v___x_65_, 2, v___f_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_ofFns(lean_object* v_onRequest_66_, lean_object* v_onFailure_67_, lean_object* v_onContinue_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_69_, 0, v_onRequest_66_);
lean_ctor_set(v___x_69_, 1, v_onFailure_67_);
lean_ctor_set(v___x_69_, 2, v_onContinue_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withFailure(lean_object* v_handler_70_, lean_object* v_onFailure_71_){
_start:
{
lean_object* v_onRequest_72_; lean_object* v_onContinue_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_onRequest_72_ = lean_ctor_get(v_handler_70_, 0);
v_onContinue_73_ = lean_ctor_get(v_handler_70_, 2);
v_isSharedCheck_80_ = !lean_is_exclusive(v_handler_70_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v_handler_70_, 1);
lean_dec(v_unused_81_);
v___x_75_ = v_handler_70_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_onContinue_73_);
lean_inc(v_onRequest_72_);
lean_dec(v_handler_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_onFailure_71_);
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_onRequest_72_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_onFailure_71_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_onContinue_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Server_Handler_withContinue(lean_object* v_handler_82_, lean_object* v_onContinue_83_){
_start:
{
lean_object* v_onRequest_84_; lean_object* v_onFailure_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_onRequest_84_ = lean_ctor_get(v_handler_82_, 0);
v_onFailure_85_ = lean_ctor_get(v_handler_82_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_handler_82_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_handler_82_, 2);
lean_dec(v_unused_93_);
v___x_87_ = v_handler_82_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_onFailure_85_);
lean_inc(v_onRequest_84_);
lean_dec(v_handler_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 2, v_onContinue_83_);
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_onRequest_84_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_onFailure_85_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_onContinue_83_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Server_Handler(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
