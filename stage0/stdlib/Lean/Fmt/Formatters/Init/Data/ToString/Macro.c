// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.ToString.Macro
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.ToString.Macro import Init.Data
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
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_strLit(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtStringInterpolation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l_Lean_Fmt_fmtStringInterpolation___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtStringInterpolation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l_Lean_Fmt_fmtStringInterpolation___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtStringInterpolation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "interpolatedStrKind"};
static const lean_object* l_Lean_Fmt_fmtStringInterpolation___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtStringInterpolation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 118, 32, 248, 73, 51, 110, 198)}};
static const lean_object* l_Lean_Fmt_fmtStringInterpolation___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtStringInterpolation___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStringInterpolation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStringInterpolation___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtStringInterpolation"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(225, 243, 124, 43, 178, 41, 135, 62)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStringInterpolation(lean_object* v_x_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_Fmt_fmtStringInterpolation___closed__1));
lean_inc(v_x_7_);
v___x_11_ = l_Lean_Syntax_isOfKind(v_x_7_, v___x_10_);
if (v___x_11_ == 0)
{
lean_object* v___x_12_; lean_object* v___x_13_; 
lean_dec(v_x_7_);
v___x_12_ = l_Lean_Fmt_Error_partialFormatter;
v___x_13_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set(v___x_13_, 1, v_a_9_);
return v___x_13_;
}
else
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_14_ = lean_unsigned_to_nat(1u);
v___x_15_ = l_Lean_Syntax_getArg(v_x_7_, v___x_14_);
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtStringInterpolation___closed__3));
lean_inc(v___x_15_);
v___x_17_ = l_Lean_Syntax_isOfKind(v___x_15_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v___x_15_);
lean_dec(v_x_7_);
v___x_18_ = l_Lean_Fmt_Error_partialFormatter;
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v_a_9_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v_sTk_21_; lean_object* v___x_22_; 
v___x_20_ = lean_unsigned_to_nat(0u);
v_sTk_21_ = l_Lean_Syntax_getArg(v_x_7_, v___x_20_);
lean_dec(v_x_7_);
v___x_22_ = l_Lean_Fmt_fmt(v_sTk_21_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v_a_24_; lean_object* v___x_25_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
lean_inc(v_a_23_);
v_a_24_ = lean_ctor_get(v___x_22_, 1);
lean_inc(v_a_24_);
lean_dec_ref_known(v___x_22_, 2);
v___x_25_ = l_Lean_Fmt_fmt(v___x_15_, v_a_8_, v_a_24_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v_a_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_35_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
v_a_27_ = lean_ctor_get(v___x_25_, 1);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_25_);
if (v_isSharedCheck_35_ == 0)
{
v___x_29_ = v___x_25_;
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_a_27_);
lean_inc(v_a_26_);
lean_dec(v___x_25_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_35_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Lean_Fmt_Layouts_strLit(v_a_23_, v_a_26_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 0, v___x_31_);
v___x_33_ = v___x_29_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_a_27_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_dec(v_a_23_);
return v___x_25_;
}
}
else
{
lean_dec(v___x_15_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtStringInterpolation___boxed(lean_object* v_x_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Fmt_fmtStringInterpolation(v_x_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1(){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_48_ = l_Lean_Fmt_fmtAttribute;
v___x_49_ = ((lean_object*)(l_Lean_Fmt_fmtStringInterpolation___closed__1));
v___x_50_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___closed__3));
v___x_51_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtStringInterpolation___boxed), 3, 0);
v___x_52_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_48_, v___x_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1___boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1();
return v_res_54_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Data_ToString_Macro_0__Lean_Fmt_fmtStringInterpolation___regBuiltin_Lean_Fmt_fmtStringInterpolation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_ToString_Macro(builtin);
}
#ifdef __cplusplus
}
#endif
