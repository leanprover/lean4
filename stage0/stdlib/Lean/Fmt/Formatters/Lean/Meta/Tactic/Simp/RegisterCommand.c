// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Meta.Tactic.Simp.RegisterCommand
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Meta.Tactic.Simp.RegisterCommand meta import Lean.Parser.Command import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "registerSimpAttr"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 136, 119, 43, 233, 213, 214, 52)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 50, 187, 249, 139, 223, 179, 152)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_4),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(101, 61, 117, 15, 84, 217, 39, 89)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_6 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_5),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(172, 140, 142, 70, 253, 39, 136, 5)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value_aux_6),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 241, 12, 130, 190, 87, 222, 88)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__7_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__8 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__8_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__9 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__9_value;
static const lean_array_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__10 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__10_value;
static const lean_string_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__11 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__11_value;
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__11_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___closed__12 = (const lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSimpAttr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtRegisterSimpAttr"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtRegisterSimpAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(83, 91, 17, 46, 87, 207, 233, 211)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSimpAttr(lean_object* v_x_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v_docComment_x3f_33_; lean_object* v___y_34_; lean_object* v___y_35_; 
v___x_30_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSimpAttr___closed__7));
lean_inc(v_x_27_);
v___x_31_ = l_Lean_Syntax_isOfKind(v_x_27_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
lean_dec(v_x_27_);
v___x_59_ = l_Lean_Fmt_Error_partialFormatter;
v___x_60_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v_a_29_);
return v___x_60_;
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = l_Lean_Syntax_getArg(v_x_27_, v___x_61_);
v___x_63_ = l_Lean_Syntax_isNone(v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; uint8_t v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_62_);
v___x_65_ = l_Lean_Syntax_matchesNull(v___x_62_, v___x_64_);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec(v___x_62_);
lean_dec(v_x_27_);
v___x_66_ = l_Lean_Fmt_Error_partialFormatter;
v___x_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_a_29_);
return v___x_67_;
}
else
{
lean_object* v_docComment_x3f_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_docComment_x3f_68_ = l_Lean_Syntax_getArg(v___x_62_, v___x_61_);
lean_dec(v___x_62_);
v___x_69_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSimpAttr___closed__12));
lean_inc(v_docComment_x3f_68_);
v___x_70_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_72_; 
lean_dec(v_docComment_x3f_68_);
lean_dec(v_x_27_);
v___x_71_ = l_Lean_Fmt_Error_partialFormatter;
v___x_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v_a_29_);
return v___x_72_;
}
else
{
lean_object* v___x_73_; 
v___x_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_73_, 0, v_docComment_x3f_68_);
v_docComment_x3f_33_ = v___x_73_;
v___y_34_ = v_a_28_;
v___y_35_ = v_a_29_;
goto v___jp_32_;
}
}
}
else
{
lean_object* v___x_74_; 
lean_dec(v___x_62_);
v___x_74_ = lean_box(0);
v_docComment_x3f_33_ = v___x_74_;
v___y_34_ = v_a_28_;
v___y_35_ = v_a_29_;
goto v___jp_32_;
}
}
v___jp_32_:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_36_ = lean_unsigned_to_nat(2u);
v___x_37_ = l_Lean_Syntax_getArg(v_x_27_, v___x_36_);
v___x_38_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSimpAttr___closed__9));
lean_inc(v___x_37_);
v___x_39_ = l_Lean_Syntax_isOfKind(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v___x_37_);
lean_dec(v_docComment_x3f_33_);
lean_dec(v_x_27_);
v___x_40_ = l_Lean_Fmt_Error_partialFormatter;
v___x_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v___y_35_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; lean_object* v_registerTk_43_; lean_object* v___x_44_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v_registerTk_43_ = l_Lean_Syntax_getArg(v_x_27_, v___x_42_);
lean_dec(v_x_27_);
v___x_44_ = l_Lean_Fmt_fmt(v_registerTk_43_, v___y_34_, v___y_35_);
if (lean_obj_tag(v___x_44_) == 0)
{
lean_object* v_a_45_; lean_object* v_a_46_; lean_object* v___x_47_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc(v_a_45_);
v_a_46_ = lean_ctor_get(v___x_44_, 1);
lean_inc(v_a_46_);
lean_dec_ref_known(v___x_44_, 2);
v___x_47_ = l_Lean_Fmt_fmt(v___x_37_, v___y_34_, v_a_46_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v_a_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
v_a_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_a_49_);
lean_dec_ref_known(v___x_47_, 2);
v___x_50_ = lean_mk_empty_array_with_capacity(v___x_36_);
v___x_51_ = lean_array_push(v___x_50_, v_a_45_);
v___x_52_ = lean_array_push(v___x_51_, v_a_48_);
v___x_53_ = 0;
v___x_54_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_54_, 0, v___x_31_);
lean_ctor_set_uint8(v___x_54_, 1, v___x_53_);
lean_ctor_set_uint8(v___x_54_, 2, v___x_53_);
lean_ctor_set_uint8(v___x_54_, 3, v___x_53_);
v___x_55_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_52_, v___x_54_);
v___x_56_ = lean_box(0);
v___x_57_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSimpAttr___closed__10));
v___x_58_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_33_, v___x_56_, v___x_57_, v___x_55_, v___y_34_, v_a_49_);
return v___x_58_;
}
else
{
lean_dec(v_a_45_);
lean_dec(v_docComment_x3f_33_);
return v___x_47_;
}
}
else
{
lean_dec(v___x_37_);
lean_dec(v_docComment_x3f_33_);
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtRegisterSimpAttr___boxed(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Fmt_fmtRegisterSimpAttr(v_x_75_, v_a_76_, v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1(){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Fmt_fmtAttribute;
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtRegisterSimpAttr___closed__7));
v___x_88_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___closed__2));
v___x_89_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtRegisterSimpAttr___boxed), 3, 0);
v___x_90_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_86_, v___x_87_, v___x_88_, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1___boxed(lean_object* v_a_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1();
return v_res_92_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand_0__Lean_Fmt_fmtRegisterSimpAttr___regBuiltin_Lean_Fmt_fmtRegisterSimpAttr__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
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
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Meta_Tactic_Simp_RegisterCommand(builtin);
}
#ifdef __cplusplus
}
#endif
