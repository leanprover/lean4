// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Parser.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Parser.Basic import Init.Data
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
lean_object* l_Lean_Fmt_fmtAtomic(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAtomic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFieldIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFieldIdx___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Fmt_fmtAtomic___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__2_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__3_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__4 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__4_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtFieldIdx"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__5 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(234, 158, 174, 248, 203, 201, 188, 155)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFieldIdx(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_Lean_Fmt_fmtAtomic(v_a_1_, v_a_2_, v_a_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtFieldIdx___boxed(lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Fmt_fmtFieldIdx(v_a_5_, v_a_6_, v_a_7_);
lean_dec_ref(v_a_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1(){
_start:
{
lean_object* v___f_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___f_21_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__0));
v___x_22_ = l_Lean_Fmt_fmtAttribute;
v___x_23_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__2));
v___x_24_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___closed__6));
v___x_25_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_22_, v___x_23_, v___x_24_, v___f_21_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1___boxed(lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1();
return v_res_27_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Parser_Basic_0__Lean_Fmt_fmtFieldIdx___regBuiltin_Lean_Fmt_fmtFieldIdx__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Parser_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
