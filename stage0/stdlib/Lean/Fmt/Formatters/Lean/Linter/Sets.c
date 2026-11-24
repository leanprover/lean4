// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Linter.Sets
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Linter.Sets meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_fill(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "command_Register_linter_set_:=_"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 210, 97, 26, 65, 126, 230, 147)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__5_value;
static const lean_array_object l_Lean_Fmt_fmtRegisterLinterSet___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__6_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__8_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterLinterSet___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__9_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterLinterSet___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLinterSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLinterSet___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtRegisterLinterSet"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterLinterSet___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 5, 173, 128, 146, 129, 66, 22)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLinterSet(lean_object* v_x_21_, lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___x_24_; uint8_t v___x_25_; lean_object* v_docComment_x3f_27_; lean_object* v___y_28_; lean_object* v___y_29_; 
v___x_24_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLinterSet___closed__3));
lean_inc(v_x_21_);
v___x_25_ = l_Lean_Syntax_isOfKind(v_x_21_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_x_21_);
v___x_75_ = l_Lean_Fmt_Error_partialFormatter;
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_23_);
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_Lean_Syntax_getArg(v_x_21_, v___x_77_);
v___x_79_ = l_Lean_Syntax_isNone(v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_78_);
v___x_81_ = l_Lean_Syntax_matchesNull(v___x_78_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
lean_dec(v___x_78_);
lean_dec(v_x_21_);
v___x_82_ = l_Lean_Fmt_Error_partialFormatter;
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_a_23_);
return v___x_83_;
}
else
{
lean_object* v_docComment_x3f_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v_docComment_x3f_84_ = l_Lean_Syntax_getArg(v___x_78_, v___x_77_);
lean_dec(v___x_78_);
v___x_85_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLinterSet___closed__10));
lean_inc(v_docComment_x3f_84_);
v___x_86_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_dec(v_docComment_x3f_84_);
lean_dec(v_x_21_);
v___x_87_ = l_Lean_Fmt_Error_partialFormatter;
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v_a_23_);
return v___x_88_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_docComment_x3f_84_);
v_docComment_x3f_27_ = v___x_89_;
v___y_28_ = v_a_22_;
v___y_29_ = v_a_23_;
goto v___jp_26_;
}
}
}
else
{
lean_object* v___x_90_; 
lean_dec(v___x_78_);
v___x_90_ = lean_box(0);
v_docComment_x3f_27_ = v___x_90_;
v___y_28_ = v_a_22_;
v___y_29_ = v_a_23_;
goto v___jp_26_;
}
}
v___jp_26_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_30_ = lean_unsigned_to_nat(2u);
v___x_31_ = l_Lean_Syntax_getArg(v_x_21_, v___x_30_);
v___x_32_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLinterSet___closed__5));
lean_inc(v___x_31_);
v___x_33_ = l_Lean_Syntax_isOfKind(v___x_31_, v___x_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v___x_31_);
lean_dec(v_docComment_x3f_27_);
lean_dec(v_x_21_);
v___x_34_ = l_Lean_Fmt_Error_partialFormatter;
v___x_35_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___y_29_);
return v___x_35_;
}
else
{
lean_object* v___x_36_; lean_object* v_registerTk_37_; lean_object* v___x_38_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v_registerTk_37_ = l_Lean_Syntax_getArg(v_x_21_, v___x_36_);
v___x_38_ = l_Lean_Fmt_fmt(v_registerTk_37_, v___y_28_, v___y_29_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v_a_40_; lean_object* v___x_41_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_a_39_);
v_a_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_a_40_);
lean_dec_ref_known(v___x_38_, 2);
v___x_41_ = l_Lean_Fmt_fmt(v___x_31_, v___y_28_, v_a_40_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v_a_43_; lean_object* v___x_44_; lean_object* v_colonEqTk_45_; lean_object* v___x_46_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_a_42_);
v_a_43_ = lean_ctor_get(v___x_41_, 1);
lean_inc(v_a_43_);
lean_dec_ref_known(v___x_41_, 2);
v___x_44_ = lean_unsigned_to_nat(3u);
v_colonEqTk_45_ = l_Lean_Syntax_getArg(v_x_21_, v___x_44_);
v___x_46_ = l_Lean_Fmt_fmt(v_colonEqTk_45_, v___y_28_, v_a_43_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v_a_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v_decls_51_; lean_object* v___x_52_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
v_a_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_46_, 2);
v___x_49_ = lean_unsigned_to_nat(4u);
v___x_50_ = l_Lean_Syntax_getArg(v_x_21_, v___x_49_);
lean_dec(v_x_21_);
v_decls_51_ = l_Lean_Syntax_getArgs(v___x_50_);
lean_dec(v___x_50_);
v___x_52_ = l_Lean_Fmt_fmtArray___redArg(v_decls_51_, v___y_28_, v_a_48_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v_a_53_; lean_object* v_a_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v_a_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc(v_a_53_);
v_a_54_ = lean_ctor_get(v___x_52_, 1);
lean_inc(v_a_54_);
lean_dec_ref_known(v___x_52_, 2);
v___x_55_ = l_Lean_Fmt_Layouts_fill(v_a_53_);
lean_dec(v_a_53_);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_30_);
v___x_57_ = lean_array_push(v___x_56_, v_a_39_);
v___x_58_ = lean_array_push(v___x_57_, v_a_42_);
v___x_59_ = 0;
v___x_60_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_60_, 0, v___x_25_);
lean_ctor_set_uint8(v___x_60_, 1, v___x_59_);
lean_ctor_set_uint8(v___x_60_, 2, v___x_59_);
lean_ctor_set_uint8(v___x_60_, 3, v___x_59_);
v___x_61_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_58_, v___x_60_);
v___x_62_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_61_, v_a_47_, v___x_55_, v___x_59_);
v___x_63_ = lean_box(0);
v___x_64_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLinterSet___closed__6));
v___x_65_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_27_, v___x_63_, v___x_64_, v___x_62_, v___y_28_, v_a_54_);
return v___x_65_;
}
else
{
lean_object* v_a_66_; lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_a_47_);
lean_dec(v_a_42_);
lean_dec(v_a_39_);
lean_dec(v_docComment_x3f_27_);
v_a_66_ = lean_ctor_get(v___x_52_, 0);
v_a_67_ = lean_ctor_get(v___x_52_, 1);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_52_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_inc(v_a_66_);
lean_dec(v___x_52_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_66_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_dec(v_a_42_);
lean_dec(v_a_39_);
lean_dec(v_docComment_x3f_27_);
lean_dec(v_x_21_);
return v___x_46_;
}
}
else
{
lean_dec(v_a_39_);
lean_dec(v_docComment_x3f_27_);
lean_dec(v_x_21_);
return v___x_41_;
}
}
else
{
lean_dec(v___x_31_);
lean_dec(v_docComment_x3f_27_);
lean_dec(v_x_21_);
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterLinterSet___boxed(lean_object* v_x_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Fmt_fmtRegisterLinterSet(v_x_91_, v_a_92_, v_a_93_);
lean_dec_ref(v_a_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1(){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_102_ = l_Lean_Fmt_fmtAttribute;
v___x_103_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterLinterSet___closed__3));
v___x_104_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___closed__2));
v___x_105_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterLinterSet___boxed), 3, 0);
v___x_106_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_102_, v___x_103_, v___x_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1___boxed(lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1();
return v_res_108_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Linter_Sets_0__Lean_Fmt_fmtRegisterLinterSet___regBuiltin_Lean_Fmt_fmtRegisterLinterSet__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Linter_Sets(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Linter_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Sets(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Sets(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Linter_Sets(builtin);
}
#ifdef __cplusplus
}
#endif
