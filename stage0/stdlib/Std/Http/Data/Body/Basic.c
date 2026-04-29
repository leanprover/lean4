// Lean compiler output
// Module: Std.Http.Data.Body.Basic
// Imports: public import Std.Async public import Std.Async.ContextAsync public import Std.Http.Data.Chunk public import Std.Http.Data.Headers public import Std.Http.Data.Body.Length
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
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_String_toUTF8___boxed(lean_object*);
static const lean_closure_object l_Std_Http_Body_instToByteArrayByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Http_Body_instToByteArrayByteArray___closed__0 = (const lean_object*)&l_Std_Http_Body_instToByteArrayByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instToByteArrayByteArray = (const lean_object*)&l_Std_Http_Body_instToByteArrayByteArray___closed__0_value;
static const lean_closure_object l_Std_Http_Body_instToByteArrayString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_toUTF8___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instToByteArrayString___closed__0 = (const lean_object*)&l_Std_Http_Body_instToByteArrayString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instToByteArrayString = (const lean_object*)&l_Std_Http_Body_instToByteArrayString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instFromByteArrayByteArray___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instFromByteArrayByteArray___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFromByteArrayByteArray___closed__0 = (const lean_object*)&l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instFromByteArrayByteArray = (const lean_object*)&l_Std_Http_Body_instFromByteArrayByteArray___closed__0_value;
static const lean_string_object l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "invalid UTF-8 encoding"};
static const lean_object* l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Body_instFromByteArrayString___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instFromByteArrayString___lam__0(lean_object*);
static const lean_closure_object l_Std_Http_Body_instFromByteArrayString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instFromByteArrayString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instFromByteArrayString___closed__0 = (const lean_object*)&l_Std_Http_Body_instFromByteArrayString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instFromByteArrayString = (const lean_object*)&l_Std_Http_Body_instFromByteArrayString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instFromByteArrayByteArray___lam__0(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v_a_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instFromByteArrayString___lam__0(lean_object* v_bs_12_){
_start:
{
uint8_t v___x_13_; 
v___x_13_ = lean_string_validate_utf8(v_bs_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; 
lean_dec_ref(v_bs_12_);
v___x_14_ = ((lean_object*)(l_Std_Http_Body_instFromByteArrayString___lam__0___closed__1));
return v___x_14_;
}
else
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_string_from_utf8_unchecked(v_bs_12_);
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
lean_object* runtime_initialize_Std_Async(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Chunk(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Body_Length(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Async(uint8_t builtin);
lean_object* initialize_Std_Async_ContextAsync(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Chunk(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Body_Length(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Async(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_ContextAsync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Chunk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Body_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
