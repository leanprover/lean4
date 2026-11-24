// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.System.IO
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.System.IO import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtPrintln___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termPrintln!__"};
static const lean_object* l_Lean_Fmt_fmtPrintln___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtPrintln___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtPrintln___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtPrintln___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 121, 220, 17, 1, 74, 122, 9)}};
static const lean_object* l_Lean_Fmt_fmtPrintln___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtPrintln___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrintln(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrintln___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtPrintln"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(72, 160, 189, 131, 92, 132, 225, 28)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrintln(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Fmt_fmtPrintln___closed__1));
lean_inc(v_x_4_);
v___x_8_ = l_Lean_Syntax_isOfKind(v_x_4_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_x_4_);
v___x_9_ = l_Lean_Fmt_Error_partialFormatter;
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_a_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_printlnTk_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v_printlnTk_12_ = l_Lean_Syntax_getArg(v_x_4_, v___x_11_);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = l_Lean_Syntax_getArg(v_x_4_, v___x_13_);
lean_dec(v_x_4_);
v___x_15_ = lean_unsigned_to_nat(2u);
v___x_16_ = lean_mk_empty_array_with_capacity(v___x_15_);
v___x_17_ = lean_array_push(v___x_16_, v_printlnTk_12_);
v___x_18_ = lean_array_push(v___x_17_, v___x_14_);
v___x_19_ = l_Lean_Fmt_fmtAppLike(v___x_18_, v_a_5_, v_a_6_);
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtPrintln___boxed(lean_object* v_x_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Fmt_fmtPrintln(v_x_20_, v_a_21_, v_a_22_);
lean_dec_ref(v_a_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1(){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_32_ = l_Lean_Fmt_fmtAttribute;
v___x_33_ = ((lean_object*)(l_Lean_Fmt_fmtPrintln___closed__1));
v___x_34_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___closed__3));
v___x_35_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtPrintln___boxed), 3, 0);
v___x_36_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_32_, v___x_33_, v___x_34_, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1___boxed(lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1();
return v_res_38_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_System_IO(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_System_IO_0__Lean_Fmt_fmtPrintln___regBuiltin_Lean_Fmt_fmtPrintln__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_System_IO(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_System_IO(builtin);
}
#ifdef __cplusplus
}
#endif
