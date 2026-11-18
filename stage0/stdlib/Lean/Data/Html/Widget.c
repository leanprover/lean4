// Lean compiler output
// Module: Lean.Data.Html.Widget
// Imports: public import Lean.Data.Html.Basic import Lean.Data.Html.Printer import Lean.Widget.UserWidget meta import Lean.Widget.UserWidget public import Lean.Message
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
lean_object* l_Lean_Html_render(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Widget_addBuiltinModule(lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_htmlWidget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 199, .m_capacity = 199, .m_length = 198, .m_data = "\nimport { createElement } from 'react'\n\nexport default function ({ html }) {\n  return createElement('span', {\n    style: { display: 'contents' },\n    dangerouslySetInnerHTML: { __html: html }\n  })\n}"};
static const lean_object* l_Lean_Html_htmlWidget___closed__0 = (const lean_object*)&l_Lean_Html_htmlWidget___closed__0_value;
static const lean_ctor_object l_Lean_Html_htmlWidget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Html_htmlWidget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 246, 172, 18, 193, 64, 23, 30)}};
static const lean_object* l_Lean_Html_htmlWidget___closed__1 = (const lean_object*)&l_Lean_Html_htmlWidget___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Html_htmlWidget = (const lean_object*)&l_Lean_Html_htmlWidget___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__0 = (const lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__0_value;
static const lean_string_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Html"};
static const lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__1 = (const lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__1_value;
static const lean_string_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "htmlWidget"};
static const lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__2 = (const lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 204, 11, 254, 52, 252, 208, 28)}};
static const lean_ctor_object l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(82, 207, 86, 14, 221, 16, 129, 125)}};
static const lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3 = (const lean_object*)&l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1();
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Html_toMessageData___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Html_toMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "html"};
static const lean_object* l_Lean_Html_toMessageData___closed__0 = (const lean_object*)&l_Lean_Html_toMessageData___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Html_toMessageData(lean_object*);
static const lean_closure_object l_Lean_Html_instToMessageData___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Html_toMessageData, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Html_instToMessageData___closed__0 = (const lean_object*)&l_Lean_Html_instToMessageData___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Html_instToMessageData = (const lean_object*)&l_Lean_Html_instToMessageData___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1(){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3));
v___x_15_ = ((lean_object*)(l_Lean_Html_htmlWidget));
v___x_16_ = l_Lean_Widget_addBuiltinModule(v___x_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___boxed(lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_toMessageData___lam__0(lean_object* v___x_19_, lean_object* v___y_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set(v___x_21_, 1, v___y_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Html_toMessageData(lean_object* v_h_23_){
_start:
{
lean_object* v___x_24_; uint64_t v_javascriptHash_25_; lean_object* v_s_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___f_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_24_ = ((lean_object*)(l_Lean_Html_htmlWidget));
v_javascriptHash_25_ = lean_ctor_get_uint64(v___x_24_, sizeof(void*)*1);
v_s_26_ = l_Lean_Html_render(v_h_23_);
v___x_27_ = ((lean_object*)(l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1___closed__3));
v___x_28_ = ((lean_object*)(l_Lean_Html_toMessageData___closed__0));
lean_inc_ref(v_s_26_);
v___x_29_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_29_, 0, v_s_26_);
v___x_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_28_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = l_Lean_Json_mkObj(v___x_32_);
lean_dec_ref_known(v___x_32_, 2);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_Html_toMessageData___lam__0), 2, 1);
lean_closure_set(v___f_34_, 0, v___x_33_);
v___x_35_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_35_, 0, v___x_27_);
lean_ctor_set(v___x_35_, 1, v___f_34_);
lean_ctor_set_uint64(v___x_35_, sizeof(void*)*2, v_javascriptHash_25_);
v___x_36_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_36_, 0, v_s_26_);
v___x_37_ = l_Lean_MessageData_ofFormat(v___x_36_);
v___x_38_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_35_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
}
lean_object* runtime_initialize_Lean_Data_Html_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Html_Printer(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* runtime_initialize_Lean_Message(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Html_Widget(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Data_Html_Widget_0__Lean_Html_htmlWidget___regBuiltin_Lean_Html_htmlWidget__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Widget_UserWidget(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Html_Widget(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Html_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Printer(uint8_t builtin);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* initialize_Lean_Widget_UserWidget(uint8_t builtin);
lean_object* initialize_Lean_Message(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Html_Widget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Html_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Printer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_UserWidget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Html_Widget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Html_Widget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Html_Widget(builtin);
}
#ifdef __cplusplus
}
#endif
