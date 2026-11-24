// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Elab.AuxDef
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Elab.AuxDef meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "aux_def"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(177, 181, 244, 12, 1, 14, 170, 235)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(83, 33, 36, 212, 17, 187, 86, 94)}};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__4_value;
static const lean_array_object l_Lean_Fmt_fmtAuxDef___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__7_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__9_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__8_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__9_value;
static const lean_string_object l_Lean_Fmt_fmtAuxDef___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__10_value;
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtAuxDef___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__11_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__10_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtAuxDef___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAuxDef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAuxDef___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fmtAuxDef"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAuxDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 125, 16, 30, 235, 218, 77, 10)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAuxDef(lean_object* v_x_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_29_ = ((lean_object*)(l_Lean_Fmt_fmtAuxDef___closed__4));
lean_inc(v_x_26_);
v___x_30_ = l_Lean_Syntax_isOfKind(v_x_26_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v_x_26_);
v___x_31_ = l_Lean_Fmt_Error_partialFormatter;
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_a_28_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v___y_35_; lean_object* v_attributes_x3f_36_; lean_object* v___y_37_; lean_object* v___y_38_; lean_object* v_docComment_x3f_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_26_, v___x_33_);
v___x_110_ = l_Lean_Syntax_isNone(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_109_);
v___x_112_ = l_Lean_Syntax_matchesNull(v___x_109_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v___x_109_);
lean_dec(v_x_26_);
v___x_113_ = l_Lean_Fmt_Error_partialFormatter;
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_28_);
return v___x_114_;
}
else
{
lean_object* v_docComment_x3f_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_docComment_x3f_115_ = l_Lean_Syntax_getArg(v___x_109_, v___x_33_);
lean_dec(v___x_109_);
v___x_116_ = ((lean_object*)(l_Lean_Fmt_fmtAuxDef___closed__11));
lean_inc(v_docComment_x3f_115_);
v___x_117_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v_docComment_x3f_115_);
lean_dec(v_x_26_);
v___x_118_ = l_Lean_Fmt_Error_partialFormatter;
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_28_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v_docComment_x3f_115_);
v_docComment_x3f_93_ = v___x_120_;
v___y_94_ = v_a_27_;
v___y_95_ = v_a_28_;
goto v___jp_92_;
}
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v___x_109_);
v___x_121_ = lean_box(0);
v_docComment_x3f_93_ = v___x_121_;
v___y_94_ = v_a_27_;
v___y_95_ = v_a_28_;
goto v___jp_92_;
}
v___jp_34_:
{
lean_object* v___x_39_; lean_object* v_auxDefTk_40_; lean_object* v___x_41_; 
v___x_39_ = lean_unsigned_to_nat(3u);
v_auxDefTk_40_ = l_Lean_Syntax_getArg(v_x_26_, v___x_39_);
v___x_41_ = l_Lean_Fmt_fmt(v_auxDefTk_40_, v___y_37_, v___y_38_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v_a_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_suggestions_46_; lean_object* v___x_47_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_a_42_);
v_a_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_41_, 2);
v___x_44_ = lean_unsigned_to_nat(4u);
v___x_45_ = l_Lean_Syntax_getArg(v_x_26_, v___x_44_);
v_suggestions_46_ = l_Lean_Syntax_getArgs(v___x_45_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Fmt_fmtArray___redArg(v_suggestions_46_, v___y_37_, v_a_43_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_50_; lean_object* v_colonTk_51_; lean_object* v___x_52_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_47_, 2);
v___x_50_ = lean_unsigned_to_nat(5u);
v_colonTk_51_ = l_Lean_Syntax_getArg(v_x_26_, v___x_50_);
v___x_52_ = l_Lean_Fmt_fmt(v_colonTk_51_, v___y_37_, v_a_49_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = lean_unsigned_to_nat(6u);
v___x_56_ = l_Lean_Syntax_getArg(v_x_26_, v___x_55_);
v___x_57_ = l_Lean_Fmt_fmt(v___x_56_, v___y_37_, v_a_54_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v_a_59_; lean_object* v___x_60_; lean_object* v_colonEqTk_61_; lean_object* v___x_62_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
v_a_59_ = lean_ctor_get(v___x_57_, 1);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_57_, 2);
v___x_60_ = lean_unsigned_to_nat(7u);
v_colonEqTk_61_ = l_Lean_Syntax_getArg(v_x_26_, v___x_60_);
v___x_62_ = l_Lean_Fmt_fmt(v_colonEqTk_61_, v___y_37_, v_a_59_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_a_63_);
v_a_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_62_, 2);
v___x_65_ = lean_unsigned_to_nat(8u);
v___x_66_ = l_Lean_Syntax_getArg(v_x_26_, v___x_65_);
v___x_67_ = l_Lean_Fmt_fmt(v___x_66_, v___y_37_, v_a_64_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
v_a_69_ = lean_ctor_get(v___x_67_, 1);
lean_inc(v_a_69_);
lean_dec_ref_known(v___x_67_, 2);
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = l_Lean_Syntax_getArg(v_x_26_, v___x_70_);
lean_dec(v_x_26_);
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_mk_empty_array_with_capacity(v___x_72_);
lean_inc_ref(v___x_73_);
v___x_74_ = lean_array_push(v___x_73_, v_a_42_);
v___x_75_ = l_Array_append___redArg(v___x_74_, v_a_48_);
lean_dec(v_a_48_);
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtAuxDef___closed__5));
v___x_77_ = l_Lean_Fmt_Layouts_globalSignature(v___x_75_, v___x_76_, v_a_53_, v_a_58_);
lean_dec_ref(v___x_75_);
v___x_78_ = 0;
v___x_79_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_77_, v_a_63_, v_a_68_, v___x_78_);
v___x_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_71_);
v___x_81_ = lean_array_push(v___x_73_, v___x_80_);
v___x_82_ = l_Lean_Fmt_fmtDeclWithModifiers(v___y_35_, v_attributes_x3f_36_, v___x_81_, v___x_79_, v___y_37_, v_a_69_);
lean_dec_ref(v___x_81_);
return v___x_82_;
}
else
{
lean_dec(v_a_63_);
lean_dec(v_a_58_);
lean_dec(v_a_53_);
lean_dec(v_a_48_);
lean_dec(v_a_42_);
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
return v___x_67_;
}
}
else
{
lean_dec(v_a_58_);
lean_dec(v_a_53_);
lean_dec(v_a_48_);
lean_dec(v_a_42_);
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
return v___x_62_;
}
}
else
{
lean_dec(v_a_53_);
lean_dec(v_a_48_);
lean_dec(v_a_42_);
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
return v___x_57_;
}
}
else
{
lean_dec(v_a_48_);
lean_dec(v_a_42_);
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
return v___x_52_;
}
}
else
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
lean_dec(v_a_42_);
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
v_a_83_ = lean_ctor_get(v___x_47_, 0);
v_a_84_ = lean_ctor_get(v___x_47_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_47_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_inc(v_a_83_);
lean_dec(v___x_47_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_89_; 
if (v_isShared_87_ == 0)
{
v___x_89_ = v___x_86_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_a_83_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_a_84_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
else
{
lean_dec(v_attributes_x3f_36_);
lean_dec(v___y_35_);
lean_dec(v_x_26_);
return v___x_41_;
}
}
v___jp_92_:
{
lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = l_Lean_Syntax_getArg(v_x_26_, v___x_96_);
v___x_98_ = l_Lean_Syntax_isNone(v___x_97_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
lean_inc(v___x_97_);
v___x_99_ = l_Lean_Syntax_matchesNull(v___x_97_, v___x_96_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v___x_97_);
lean_dec(v_docComment_x3f_93_);
lean_dec(v_x_26_);
v___x_100_ = l_Lean_Fmt_Error_partialFormatter;
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___y_95_);
return v___x_101_;
}
else
{
lean_object* v_attributes_x3f_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_attributes_x3f_102_ = l_Lean_Syntax_getArg(v___x_97_, v___x_33_);
lean_dec(v___x_97_);
v___x_103_ = ((lean_object*)(l_Lean_Fmt_fmtAuxDef___closed__9));
lean_inc(v_attributes_x3f_102_);
v___x_104_ = l_Lean_Syntax_isOfKind(v_attributes_x3f_102_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_attributes_x3f_102_);
lean_dec(v_docComment_x3f_93_);
lean_dec(v_x_26_);
v___x_105_ = l_Lean_Fmt_Error_partialFormatter;
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v___y_95_);
return v___x_106_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_attributes_x3f_102_);
v___y_35_ = v_docComment_x3f_93_;
v_attributes_x3f_36_ = v___x_107_;
v___y_37_ = v___y_94_;
v___y_38_ = v___y_95_;
goto v___jp_34_;
}
}
}
else
{
lean_object* v___x_108_; 
lean_dec(v___x_97_);
v___x_108_ = lean_box(0);
v___y_35_ = v_docComment_x3f_93_;
v_attributes_x3f_36_ = v___x_108_;
v___y_37_ = v___y_94_;
v___y_38_ = v___y_95_;
goto v___jp_34_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAuxDef___boxed(lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Fmt_fmtAuxDef(v_x_122_, v_a_123_, v_a_124_);
lean_dec_ref(v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1(){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = l_Lean_Fmt_fmtAttribute;
v___x_134_ = ((lean_object*)(l_Lean_Fmt_fmtAuxDef___closed__4));
v___x_135_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___closed__2));
v___x_136_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAuxDef___boxed), 3, 0);
v___x_137_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_133_, v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1___boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1();
return v_res_139_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Elab_AuxDef_0__Lean_Fmt_fmtAuxDef___regBuiltin_Lean_Fmt_fmtAuxDef__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_AuxDef(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Elab_AuxDef(builtin);
}
#ifdef __cplusplus
}
#endif
