// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Data.Html.Elab
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Data.Html.Elab import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtHtmlCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtHtmlCmd___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtHtmlCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtHtmlCmd___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtHtmlCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Html"};
static const lean_object* l_Lean_Fmt_fmtHtmlCmd___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtHtmlCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "htmlCmd"};
static const lean_object* l_Lean_Fmt_fmtHtmlCmd___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 184, 34, 41, 228, 163, 106, 158)}};
static const lean_ctor_object l_Lean_Fmt_fmtHtmlCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(236, 154, 156, 19, 183, 24, 205, 153)}};
static const lean_object* l_Lean_Fmt_fmtHtmlCmd___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHtmlCmd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHtmlCmd___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtHtmlCmd"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtHtmlCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(57, 131, 154, 176, 187, 241, 224, 137)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHtmlCmd(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtHtmlCmd___closed__4));
lean_inc(v_x_10_);
v___x_14_ = l_Lean_Syntax_isOfKind(v_x_10_, v___x_13_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
lean_dec(v_x_10_);
v___x_15_ = l_Lean_Fmt_Error_partialFormatter;
v___x_16_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v_a_12_);
return v___x_16_;
}
else
{
lean_object* v___x_17_; lean_object* v_htmlTk_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_htmlTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = l_Lean_Fmt_fmt(v_htmlTk_18_, v_a_11_, v_a_12_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_a_21_);
lean_dec_ref_known(v___x_19_, 2);
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_10_, v___x_22_);
lean_dec(v_x_10_);
v___x_24_ = l_Lean_Fmt_fmt(v___x_23_, v_a_11_, v_a_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_40_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_a_26_ = lean_ctor_get(v___x_24_, 1);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_40_ == 0)
{
v___x_28_ = v___x_24_;
v_isShared_29_ = v_isSharedCheck_40_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_40_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; uint8_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = lean_mk_empty_array_with_capacity(v___x_30_);
v___x_32_ = lean_array_push(v___x_31_, v_a_20_);
v___x_33_ = lean_array_push(v___x_32_, v_a_25_);
v___x_34_ = 0;
v___x_35_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_35_, 0, v___x_14_);
lean_ctor_set_uint8(v___x_35_, 1, v___x_34_);
lean_ctor_set_uint8(v___x_35_, 2, v___x_34_);
lean_ctor_set_uint8(v___x_35_, 3, v___x_34_);
v___x_36_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_33_, v___x_35_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 0, v___x_36_);
v___x_38_ = v___x_28_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_a_26_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_dec(v_a_20_);
return v___x_24_;
}
}
else
{
lean_dec(v_x_10_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtHtmlCmd___boxed(lean_object* v_x_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Fmt_fmtHtmlCmd(v_x_41_, v_a_42_, v_a_43_);
lean_dec_ref(v_a_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_52_ = l_Lean_Fmt_fmtAttribute;
v___x_53_ = ((lean_object*)(l_Lean_Fmt_fmtHtmlCmd___closed__4));
v___x_54_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___closed__2));
v___x_55_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtHtmlCmd___boxed), 3, 0);
v___x_56_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_52_, v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1___boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1();
return v_res_58_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Data_Html_Elab_0__Lean_Fmt_fmtHtmlCmd___regBuiltin_Lean_Fmt_fmtHtmlCmd__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Data_Html_Elab(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Html_Elab(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Data_Html_Elab(builtin);
}
#ifdef __cplusplus
}
#endif
