// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Tactic.Grind.EMatch
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Util.Trace meta import Lean.Meta.Tactic.Grind.EMatch import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTraceTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "EMatch"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "doElemReportEMatchIssue!__"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(129, 198, 51, 239, 67, 103, 255, 17)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__4_value),LEAN_SCALAR_PTR_LITERAL(183, 190, 197, 223, 133, 54, 108, 160)}};
static const lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "fmtDoElemReportEMatchIssue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 18, 22, 230, 76, 211, 205, 119)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5));
lean_inc(v_x_12_);
v___x_16_ = l_Lean_Syntax_isOfKind(v_x_12_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_x_12_);
v___x_17_ = l_Lean_Fmt_Error_partialFormatter;
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v_a_14_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v_reportTk_20_; lean_object* v___x_21_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v_reportTk_20_ = l_Lean_Syntax_getArg(v_x_12_, v___x_19_);
v___x_21_ = l_Lean_Fmt_fmt(v_reportTk_20_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v_a_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
v_a_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_a_23_);
lean_dec_ref_known(v___x_21_, 2);
v___x_24_ = lean_unsigned_to_nat(1u);
v___x_25_ = l_Lean_Syntax_getArg(v_x_12_, v___x_24_);
lean_dec(v_x_12_);
v___x_26_ = l_Lean_Fmt_fmtTraceTerm(v_a_22_, v___x_25_, v_a_13_, v_a_23_);
return v___x_26_;
}
else
{
lean_dec(v_x_12_);
return v___x_21_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportEMatchIssue___boxed(lean_object* v_x_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Fmt_fmtDoElemReportEMatchIssue(v_x_27_, v_a_28_, v_a_29_);
lean_dec_ref(v_a_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1(){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_38_ = l_Lean_Fmt_fmtAttribute;
v___x_39_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportEMatchIssue___closed__5));
v___x_40_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___closed__2));
v___x_41_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoElemReportEMatchIssue___boxed), 3, 0);
v___x_42_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_38_, v___x_39_, v___x_40_, v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1___boxed(lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1();
return v_res_44_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch_0__Lean_Fmt_fmtDoElemReportEMatchIssue___regBuiltin_Lean_Fmt_fmtDoElemReportEMatchIssue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Grind_EMatch(builtin);
}
#ifdef __cplusplus
}
#endif
