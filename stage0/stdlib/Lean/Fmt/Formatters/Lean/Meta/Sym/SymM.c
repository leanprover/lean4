// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Sym.SymM
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Lean.Util.Trace meta import Lean.Meta.Sym.SymM import Init.Data
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
lean_object* l_Lean_Fmt_fmtTraceTerm(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportIssue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportIssue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportIssue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportIssue___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtDoElemReportIssue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "doElemReportIssue!__"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportIssue___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(28, 149, 154, 203, 214, 83, 169, 43)}};
static const lean_object* l_Lean_Fmt_fmtDoElemReportIssue___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportIssue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportIssue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtDoElemReportIssue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(57, 60, 209, 128, 33, 10, 69, 36)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "doElemReportDbgIssue!__"};
static const lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 157, 148, 19, 62, 70, 252, 55)}};
static const lean_ctor_object l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 81, 179, 30, 51, 192, 195, 77)}};
static const lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "fmtDoElemReportDbgIssue"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDoElemReportIssue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 208, 116, 49, 149, 185, 191, 1)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportIssue(lean_object* v_x_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_13_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportIssue___closed__4));
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
lean_object* v___x_17_; lean_object* v_reportTk_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v_reportTk_18_ = l_Lean_Syntax_getArg(v_x_10_, v___x_17_);
v___x_19_ = l_Lean_Fmt_fmt(v_reportTk_18_, v_a_11_, v_a_12_);
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
v___x_24_ = l_Lean_Fmt_fmtTraceTerm(v_a_20_, v___x_23_, v_a_11_, v_a_21_);
return v___x_24_;
}
else
{
lean_dec(v_x_10_);
return v___x_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportIssue___boxed(lean_object* v_x_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Fmt_fmtDoElemReportIssue(v_x_25_, v_a_26_, v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1(){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_36_ = l_Lean_Fmt_fmtAttribute;
v___x_37_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportIssue___closed__4));
v___x_38_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___closed__2));
v___x_39_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoElemReportIssue___boxed), 3, 0);
v___x_40_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_36_, v___x_37_, v___x_38_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1___boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_52_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1));
lean_inc(v_x_49_);
v___x_53_ = l_Lean_Syntax_isOfKind(v_x_49_, v___x_52_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_x_49_);
v___x_54_ = l_Lean_Fmt_Error_partialFormatter;
v___x_55_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v_a_51_);
return v___x_55_;
}
else
{
lean_object* v___x_56_; lean_object* v_reportTk_57_; lean_object* v___x_58_; 
v___x_56_ = lean_unsigned_to_nat(0u);
v_reportTk_57_ = l_Lean_Syntax_getArg(v_x_49_, v___x_56_);
v___x_58_ = l_Lean_Fmt_fmt(v_reportTk_57_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v_a_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
v_a_60_ = lean_ctor_get(v___x_58_, 1);
lean_inc(v_a_60_);
lean_dec_ref_known(v___x_58_, 2);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = l_Lean_Syntax_getArg(v_x_49_, v___x_61_);
lean_dec(v_x_49_);
v___x_63_ = l_Lean_Fmt_fmtTraceTerm(v_a_59_, v___x_62_, v_a_50_, v_a_60_);
return v___x_63_;
}
else
{
lean_dec(v_x_49_);
return v___x_58_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDoElemReportDbgIssue___boxed(lean_object* v_x_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Fmt_fmtDoElemReportDbgIssue(v_x_64_, v_a_65_, v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1(){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = l_Lean_Fmt_fmtAttribute;
v___x_75_ = ((lean_object*)(l_Lean_Fmt_fmtDoElemReportDbgIssue___closed__1));
v___x_76_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___closed__1));
v___x_77_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDoElemReportDbgIssue___boxed), 3, 0);
v___x_78_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_74_, v___x_75_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1___boxed(lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1();
return v_res_80_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportIssue___regBuiltin_Lean_Fmt_fmtDoElemReportIssue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM_0__Lean_Fmt_fmtDoElemReportDbgIssue___regBuiltin_Lean_Fmt_fmtDoElemReportDbgIssue__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_Trace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Sym_SymM(builtin);
}
#ifdef __cplusplus
}
#endif
