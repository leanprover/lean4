// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.LabelAttribute
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.LabelAttribute meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "registerLabelAttr"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(137, 219, 247, 230, 185, 4, 38, 139)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 77, 82, 99, 253, 53, 120, 77)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 175, 252, 253, 79, 201, 79, 236)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(124, 1, 33, 142, 116, 70, 52, 42)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value_aux_4),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(221, 58, 2, 223, 33, 1, 81, 38)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__7_value;
static const lean_array_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLabelAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtRegisterLabelAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLabelAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 232, 22, 108, 75, 135, 36, 121)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLabelAttr(lean_object* v_x_23_, lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___x_26_; uint8_t v___x_27_; lean_object* v_docComment_x3f_29_; lean_object* v___y_30_; lean_object* v___y_31_; 
v___x_26_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLabelAttr___closed__5));
lean_inc(v_x_23_);
v___x_27_ = l_Lean_Syntax_isOfKind(v_x_23_, v___x_26_);
if (v___x_27_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_x_23_);
v___x_55_ = l_Lean_Fmt_Error_partialFormatter;
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v_a_25_);
return v___x_56_;
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_Syntax_getArg(v_x_23_, v___x_57_);
v___x_59_ = l_Lean_Syntax_isNone(v___x_58_);
if (v___x_59_ == 0)
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_58_);
v___x_61_ = l_Lean_Syntax_matchesNull(v___x_58_, v___x_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v___x_58_);
lean_dec(v_x_23_);
v___x_62_ = l_Lean_Fmt_Error_partialFormatter;
v___x_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v_a_25_);
return v___x_63_;
}
else
{
lean_object* v_docComment_x3f_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_docComment_x3f_64_ = l_Lean_Syntax_getArg(v___x_58_, v___x_57_);
lean_dec(v___x_58_);
v___x_65_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLabelAttr___closed__10));
lean_inc(v_docComment_x3f_64_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_64_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_docComment_x3f_64_);
lean_dec(v_x_23_);
v___x_67_ = l_Lean_Fmt_Error_partialFormatter;
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_25_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v_docComment_x3f_64_);
v_docComment_x3f_29_ = v___x_69_;
v___y_30_ = v_a_24_;
v___y_31_ = v_a_25_;
goto v___jp_28_;
}
}
}
else
{
lean_object* v___x_70_; 
lean_dec(v___x_58_);
v___x_70_ = lean_box(0);
v_docComment_x3f_29_ = v___x_70_;
v___y_30_ = v_a_24_;
v___y_31_ = v_a_25_;
goto v___jp_28_;
}
}
v___jp_28_:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_32_ = lean_unsigned_to_nat(2u);
v___x_33_ = l_Lean_Syntax_getArg(v_x_23_, v___x_32_);
v___x_34_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLabelAttr___closed__7));
lean_inc(v___x_33_);
v___x_35_ = l_Lean_Syntax_isOfKind(v___x_33_, v___x_34_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v___x_33_);
lean_dec(v_docComment_x3f_29_);
lean_dec(v_x_23_);
v___x_36_ = l_Lean_Fmt_Error_partialFormatter;
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___y_31_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_registerTk_39_; lean_object* v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v_registerTk_39_ = l_Lean_Syntax_getArg(v_x_23_, v___x_38_);
lean_dec(v_x_23_);
v___x_40_ = l_Lean_Fmt_fmt(v_registerTk_39_, v___y_30_, v___y_31_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v_a_42_; lean_object* v___x_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
v_a_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_a_42_);
lean_dec_ref_known(v___x_40_, 2);
v___x_43_ = l_Lean_Fmt_fmt(v___x_33_, v___y_30_, v_a_42_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
v_a_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_43_, 2);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_47_ = lean_array_push(v___x_46_, v_a_41_);
v___x_48_ = lean_array_push(v___x_47_, v_a_44_);
v___x_49_ = 0;
v___x_50_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_50_, 0, v___x_27_);
lean_ctor_set_uint8(v___x_50_, 1, v___x_49_);
lean_ctor_set_uint8(v___x_50_, 2, v___x_49_);
lean_ctor_set_uint8(v___x_50_, 3, v___x_49_);
v___x_51_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_48_, v___x_50_);
v___x_52_ = lean_box(0);
v___x_53_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLabelAttr___closed__8));
v___x_54_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_29_, v___x_52_, v___x_53_, v___x_51_, v___y_30_, v_a_45_);
return v___x_54_;
}
else
{
lean_dec(v_a_41_);
lean_dec(v_docComment_x3f_29_);
return v___x_43_;
}
}
else
{
lean_dec(v___x_33_);
lean_dec(v_docComment_x3f_29_);
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLabelAttr___boxed(lean_object* v_x_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Fmt_fmtRegisterLabelAttr(v_x_71_, v_a_72_, v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_82_ = l_Lean_Fmt_fmtAttribute;
v___x_83_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLabelAttr___closed__5));
v___x_84_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___closed__2));
v___x_85_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterLabelAttr___boxed), 3, 0);
v___x_86_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_82_, v___x_83_, v___x_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1___boxed(lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1();
return v_res_88_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_LabelAttribute_0__Lean_Fmt_fmtRegisterLabelAttr___regBuiltin_Lean_Fmt_fmtRegisterLabelAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_LabelAttribute(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LabelAttribute(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_LabelAttribute(builtin);
}
#ifdef __cplusplus
}
#endif
