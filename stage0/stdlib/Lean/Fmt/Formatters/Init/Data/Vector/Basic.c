// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.Vector.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.Vector.Basic import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtVectorLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Vector"};
static const lean_object* l_Lean_Fmt_fmtVectorLit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtVectorLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term#v[_,]"};
static const lean_object* l_Lean_Fmt_fmtVectorLit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtVectorLit___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 122, 98, 30, 71, 224, 237, 30)}};
static const lean_ctor_object l_Lean_Fmt_fmtVectorLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__1_value),LEAN_SCALAR_PTR_LITERAL(222, 133, 146, 175, 235, 143, 200, 186)}};
static const lean_object* l_Lean_Fmt_fmtVectorLit___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtVectorLit___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVectorLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVectorLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtVectorLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(18, 196, 42, 163, 9, 242, 213, 249)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVectorLit(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtVectorLit___closed__2));
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
lean_object* v___x_13_; lean_object* v_lbTk_14_; lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v_rbTk_18_; lean_object* v_elems_19_; lean_object* v___x_20_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_lbTk_14_ = l_Lean_Syntax_getArg(v_x_6_, v___x_13_);
v___x_15_ = lean_unsigned_to_nat(1u);
v___x_16_ = l_Lean_Syntax_getArg(v_x_6_, v___x_15_);
v___x_17_ = lean_unsigned_to_nat(2u);
v_rbTk_18_ = l_Lean_Syntax_getArg(v_x_6_, v___x_17_);
lean_dec(v_x_6_);
v_elems_19_ = l_Lean_Syntax_getArgs(v___x_16_);
lean_dec(v___x_16_);
v___x_20_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_14_, v_elems_19_, v_rbTk_18_, v_a_7_, v_a_8_);
lean_dec_ref(v_elems_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtVectorLit___boxed(lean_object* v_x_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Fmt_fmtVectorLit(v_x_21_, v_a_22_, v_a_23_);
lean_dec_ref(v_a_22_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1(){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_33_ = l_Lean_Fmt_fmtAttribute;
v___x_34_ = ((lean_object*)(l_Lean_Fmt_fmtVectorLit___closed__2));
v___x_35_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___closed__3));
v___x_36_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtVectorLit___boxed), 3, 0);
v___x_37_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_33_, v___x_34_, v___x_35_, v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1___boxed(lean_object* v_a_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1();
return v_res_39_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Data_Vector_Basic_0__Lean_Fmt_fmtVectorLit___regBuiltin_Lean_Fmt_fmtVectorLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_Vector_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
