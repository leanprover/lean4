// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Exception
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Exception import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtThrowError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtThrowError___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtThrowError___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtThrowError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "termThrowError__"};
static const lean_object* l_Lean_Fmt_fmtThrowError___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtThrowError___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtThrowError___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtThrowError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 45, 105, 121, 242, 5, 105, 46)}};
static const lean_object* l_Lean_Fmt_fmtThrowError___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtThrowError___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowError___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtThrowError"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 191, 237, 7, 166, 251, 45, 28)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtThrowErrorAt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "termThrowErrorAt____"};
static const lean_object* l_Lean_Fmt_fmtThrowErrorAt___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtThrowErrorAt___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtThrowErrorAt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtThrowErrorAt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtThrowErrorAt___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtThrowErrorAt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(219, 135, 54, 14, 35, 246, 144, 68)}};
static const lean_object* l_Lean_Fmt_fmtThrowErrorAt___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtThrowErrorAt___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowErrorAt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowErrorAt___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "fmtThrowErrorAt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtThrowError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 29, 135, 79, 58, 165, 235, 230)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowError(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtThrowError___closed__2));
lean_inc(v_x_6_);
v___x_10_ = l_Lean_Syntax_isOfKind(v_x_6_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec(v_x_6_);
v___x_11_ = l_Lean_Fmt_Error_partialFormatter;
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_a_8_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v_throwErrorTk_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_throwErrorTk_14_ = l_Lean_Syntax_getArg(v_x_6_, v___x_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = l_Lean_Syntax_getArg(v_x_6_, v___x_15_);
lean_dec(v_x_6_);
v___x_17_ = lean_unsigned_to_nat(2u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_array_push(v___x_18_, v_throwErrorTk_14_);
v___x_20_ = lean_array_push(v___x_19_, v___x_16_);
v___x_21_ = l_Lean_Fmt_fmtAppLike(v___x_20_, v_a_7_, v_a_8_);
return v___x_21_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowError___boxed(lean_object* v_x_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Fmt_fmtThrowError(v_x_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_a_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1(){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_33_ = l_Lean_Fmt_fmtAttribute;
v___x_34_ = ((lean_object*)(l_Lean_Fmt_fmtThrowError___closed__2));
v___x_35_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___closed__2));
v___x_36_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtThrowError___boxed), 3, 0);
v___x_37_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_33_, v___x_34_, v___x_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1___boxed(lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1();
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowErrorAt(lean_object* v_x_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Fmt_fmtThrowErrorAt___closed__1));
lean_inc(v_x_44_);
v___x_48_ = l_Lean_Syntax_isOfKind(v_x_44_, v___x_47_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_x_44_);
v___x_49_ = l_Lean_Fmt_Error_partialFormatter;
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v_a_46_);
return v___x_50_;
}
else
{
lean_object* v___x_51_; lean_object* v_throwErrorAtTk_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_51_ = lean_unsigned_to_nat(0u);
v_throwErrorAtTk_52_ = l_Lean_Syntax_getArg(v_x_44_, v___x_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = l_Lean_Syntax_getArg(v_x_44_, v___x_53_);
v___x_55_ = lean_unsigned_to_nat(2u);
v___x_56_ = l_Lean_Syntax_getArg(v_x_44_, v___x_55_);
lean_dec(v_x_44_);
v___x_57_ = lean_unsigned_to_nat(3u);
v___x_58_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_59_ = lean_array_push(v___x_58_, v_throwErrorAtTk_52_);
v___x_60_ = lean_array_push(v___x_59_, v___x_54_);
v___x_61_ = lean_array_push(v___x_60_, v___x_56_);
v___x_62_ = l_Lean_Fmt_fmtAppLike(v___x_61_, v_a_45_, v_a_46_);
return v___x_62_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtThrowErrorAt___boxed(lean_object* v_x_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Fmt_fmtThrowErrorAt(v_x_63_, v_a_64_, v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = l_Lean_Fmt_fmtAttribute;
v___x_74_ = ((lean_object*)(l_Lean_Fmt_fmtThrowErrorAt___closed__1));
v___x_75_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___closed__1));
v___x_76_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtThrowErrorAt___boxed), 3, 0);
v___x_77_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_73_, v___x_74_, v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1___boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1();
return v_res_79_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Exception(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowError___regBuiltin_Lean_Fmt_fmtThrowError__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Exception_0__Lean_Fmt_fmtThrowErrorAt___regBuiltin_Lean_Fmt_fmtThrowErrorAt__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Exception(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Exception(builtin);
}
#ifdef __cplusplus
}
#endif
