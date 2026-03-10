// Lean compiler output
// Module: Std.Internal.Http.Internal.Encode
// Imports: public import Std.Internal.Http.Internal.ChunkedBuffer public import Std.Internal.Http.Data.Version
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
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/1.1"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/2.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2_value;
static const lean_string_object l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "HTTP/3.0"};
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3_value;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_instEncodeV11Version___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_instEncodeV11Version___closed__0 = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Internal_instEncodeV11Version = (const lean_object*)&l_Std_Http_Internal_instEncodeV11Version___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
switch (x_2) {
case 0:
{
lean_object* x_18; 
x_18 = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__0));
x_3 = x_18;
goto block_17;
}
case 1:
{
lean_object* x_19; 
x_19 = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__1));
x_3 = x_19;
goto block_17;
}
case 2:
{
lean_object* x_20; 
x_20 = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__2));
x_3 = x_20;
goto block_17;
}
default: 
{
lean_object* x_21; 
x_21 = ((lean_object*)(l_Std_Http_Internal_instEncodeV11Version___lam__0___closed__3));
x_3 = x_21;
goto block_17;
}
}
block_17:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_16; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
x_6 = x_1;
x_7 = x_16;
goto block_15;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_string_to_utf8(x_3);
lean_dec_ref(x_3);
lean_inc_ref(x_8);
x_9 = lean_array_push(x_4, x_8);
x_10 = lean_byte_array_size(x_8);
lean_dec_ref(x_8);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_11);
lean_ctor_set(x_6, 0, x_9);
x_12 = x_6;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_instEncodeV11Version___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Std_Http_Internal_instEncodeV11Version___lam__0(x_1, x_3);
return x_4;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Internal_ChunkedBuffer(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Internal_ChunkedBuffer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Version(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Internal_ChunkedBuffer(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Version(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Internal_Encode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Internal_ChunkedBuffer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Version(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Internal_Encode(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Internal_Encode(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Internal_Encode(builtin);
}
#ifdef __cplusplus
}
#endif
