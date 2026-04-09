// Lean compiler output
// Module: Init.Data.Ord.String
// Imports: public import Init.Data.Order.Ord public import Init.Data.String.Basic import Init.Data.Char.Lemmas import Init.Data.String.Lemmas.StringOrder
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
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_instOrd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_instOrd___closed__0 = (const lean_object*)&l_String_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_String_instOrd = (const lean_object*)&l_String_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_String_instOrd___lam__0(lean_object* v_x_1_, lean_object* v_y_2_){
_start:
{
uint8_t v___x_3_; 
v___x_3_ = lean_string_dec_lt(v_x_1_, v_y_2_);
if (v___x_3_ == 0)
{
uint8_t v___x_4_; 
v___x_4_ = lean_string_dec_eq(v_x_1_, v_y_2_);
if (v___x_4_ == 0)
{
uint8_t v___x_5_; 
v___x_5_ = 2;
return v___x_5_;
}
else
{
uint8_t v___x_6_; 
v___x_6_ = 1;
return v___x_6_;
}
}
else
{
uint8_t v___x_7_; 
v___x_7_ = 0;
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l_String_instOrd___lam__0___boxed(lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_String_instOrd___lam__0(v_x_8_, v_y_9_);
lean_dec_ref(v_y_9_);
lean_dec_ref(v_x_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_StringOrder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_String(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_StringOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_String(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Char_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_StringOrder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Char_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_StringOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_String(builtin);
}
#ifdef __cplusplus
}
#endif
