// Lean compiler output
// Module: Std.Http.Internal.Encode
// Imports: public import Std.Http.Internal.ChunkedBuffer public import Std.Http.Data.Version
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
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11Version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11Version = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object* v_buffer_5_, uint8_t v___y_6_){
_start:
{
lean_object* v___y_8_; 
switch(v___y_6_)
{
case 0:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0));
v___y_8_ = v___x_22_;
goto v___jp_7_;
}
case 1:
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1));
v___y_8_ = v___x_23_;
goto v___jp_7_;
}
case 2:
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2));
v___y_8_ = v___x_24_;
goto v___jp_7_;
}
default: 
{
lean_object* v___x_25_; 
v___x_25_ = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3));
v___y_8_ = v___x_25_;
goto v___jp_7_;
}
}
v___jp_7_:
{
lean_object* v_data_9_; lean_object* v_size_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_21_; 
v_data_9_ = lean_ctor_get(v_buffer_5_, 0);
v_size_10_ = lean_ctor_get(v_buffer_5_, 1);
v_isSharedCheck_21_ = !lean_is_exclusive(v_buffer_5_);
if (v_isSharedCheck_21_ == 0)
{
v___x_12_ = v_buffer_5_;
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_size_10_);
lean_inc(v_data_9_);
lean_dec(v_buffer_5_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_21_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_19_; 
v___x_14_ = lean_string_to_utf8(v___y_8_);
lean_inc_ref(v___x_14_);
v___x_15_ = lean_array_push(v_data_9_, v___x_14_);
v___x_16_ = lean_byte_array_size(v___x_14_);
lean_dec_ref(v___x_14_);
v___x_17_ = lean_nat_add(v_size_10_, v___x_16_);
lean_dec(v_size_10_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 1, v___x_17_);
lean_ctor_set(v___x_12_, 0, v___x_15_);
v___x_19_ = v___x_12_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_15_);
lean_ctor_set(v_reuseFailAlloc_20_, 1, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object* v_buffer_26_, lean_object* v___y_27_){
_start:
{
uint8_t v___y_52__boxed_28_; lean_object* v_res_29_; 
v___y_52__boxed_28_ = lean_unbox(v___y_27_);
v_res_29_ = l_Std_Http_Internal_instEncodeV11Version___lam__0(v_buffer_26_, v___y_52__boxed_28_);
return v_res_29_;
}
}
lean_object* runtime_initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Version(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Http_Internal_ChunkedBuffer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Internal_ChunkedBuffer(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Version(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Internal_ChunkedBuffer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Internal_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Internal_Encode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Internal_Encode(builtin);
}
#ifdef __cplusplus
}
#endif
