// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.WP.Triple.Basic
// Imports: public import Lean.Fmt.FmtM.Basic public import Lean.Fmt.Formatters.Std.Do.Triple.Basic meta import Std.WP.Triple.Basic import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtNamedArgumentTerm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_hoareTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTripleNotation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTripleNotation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTripleNotation___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "tripleNotation"};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtTripleNotation___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTripleNotation___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Fmt_fmtTripleNotation___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__2_value),LEAN_SCALAR_PTR_LITERAL(203, 53, 36, 30, 160, 173, 44, 79)}};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtTripleNotation___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtTripleNotation___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtTripleNotation___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleNotation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleNotation___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtTripleNotation"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 49, 197, 199, 34, 199, 208, 96)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTripleExceptPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tripleExceptPost"};
static const lean_object* l_Lean_Fmt_fmtTripleExceptPost___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTripleExceptPost___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtTripleExceptPost___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTripleExceptPost___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTripleExceptPost___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTripleNotation___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Fmt_fmtTripleExceptPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTripleExceptPost___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTripleExceptPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 247, 187, 229, 229, 170, 136, 174)}};
static const lean_object* l_Lean_Fmt_fmtTripleExceptPost___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTripleExceptPost___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleExceptPost(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleExceptPost___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "fmtTripleExceptPost"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 47, 71, 64, 246, 26, 200, 214)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleNotation(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lean_Fmt_fmtTripleNotation___closed__3));
lean_inc(v_x_11_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_11_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_x_11_);
v___x_16_ = l_Lean_Fmt_Error_partialFormatter;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_a_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v_preLbTk_19_; lean_object* v___x_20_; lean_object* v___y_22_; lean_object* v___y_23_; lean_object* v___y_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___y_28_; lean_object* v___y_29_; lean_object* v___y_30_; lean_object* v___y_31_; lean_object* v___y_32_; lean_object* v___y_33_; lean_object* v___y_34_; lean_object* v___y_35_; lean_object* v___y_62_; lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v___y_67_; lean_object* v___y_68_; lean_object* v___y_69_; lean_object* v___y_70_; lean_object* v___y_71_; lean_object* v___y_72_; lean_object* v___y_73_; lean_object* v___y_74_; lean_object* v___y_75_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_preRbTk_87_; lean_object* v_mLbTk_x3f_89_; lean_object* v_m_x3f_90_; lean_object* v_mColonEqTk_x3f_91_; lean_object* v_mVal_x3f_92_; lean_object* v_mRbTk_x3f_93_; lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v_preLbTk_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_11_, v___x_20_);
v___x_86_ = lean_unsigned_to_nat(2u);
v_preRbTk_87_ = l_Lean_Syntax_getArg(v_x_11_, v___x_86_);
v___x_122_ = lean_unsigned_to_nat(3u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_11_, v___x_122_);
v___x_124_ = l_Lean_Syntax_isNone(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_123_);
v___x_126_ = l_Lean_Syntax_matchesNull(v___x_123_, v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v___x_123_);
lean_dec(v_preRbTk_87_);
lean_dec(v___x_85_);
lean_dec(v_preLbTk_19_);
lean_dec(v_x_11_);
v___x_127_ = l_Lean_Fmt_Error_partialFormatter;
v___x_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v_a_13_);
return v___x_128_;
}
else
{
lean_object* v_m_x3f_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_m_x3f_129_ = l_Lean_Syntax_getArg(v___x_123_, v___x_20_);
v___x_130_ = ((lean_object*)(l_Lean_Fmt_fmtTripleNotation___closed__5));
lean_inc(v_m_x3f_129_);
v___x_131_ = l_Lean_Syntax_isOfKind(v_m_x3f_129_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_m_x3f_129_);
lean_dec(v___x_123_);
lean_dec(v_preRbTk_87_);
lean_dec(v___x_85_);
lean_dec(v_preLbTk_19_);
lean_dec(v_x_11_);
v___x_132_ = l_Lean_Fmt_Error_partialFormatter;
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_13_);
return v___x_133_;
}
else
{
lean_object* v_mLbTk_x3f_134_; lean_object* v_mColonEqTk_x3f_135_; lean_object* v_mVal_x3f_136_; lean_object* v___x_137_; lean_object* v_mRbTk_x3f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_mLbTk_x3f_134_ = l_Lean_Syntax_getArg(v___x_123_, v___x_18_);
v_mColonEqTk_x3f_135_ = l_Lean_Syntax_getArg(v___x_123_, v___x_86_);
v_mVal_x3f_136_ = l_Lean_Syntax_getArg(v___x_123_, v___x_122_);
v___x_137_ = lean_unsigned_to_nat(4u);
v_mRbTk_x3f_138_ = l_Lean_Syntax_getArg(v___x_123_, v___x_137_);
lean_dec(v___x_123_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_mLbTk_x3f_134_);
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_m_x3f_129_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_mColonEqTk_x3f_135_);
v___x_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_142_, 0, v_mVal_x3f_136_);
v___x_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_143_, 0, v_mRbTk_x3f_138_);
v_mLbTk_x3f_89_ = v___x_139_;
v_m_x3f_90_ = v___x_140_;
v_mColonEqTk_x3f_91_ = v___x_141_;
v_mVal_x3f_92_ = v___x_142_;
v_mRbTk_x3f_93_ = v___x_143_;
v___y_94_ = v_a_12_;
v___y_95_ = v_a_13_;
goto v___jp_88_;
}
}
}
else
{
lean_object* v___x_144_; 
lean_dec(v___x_123_);
v___x_144_ = lean_box(0);
v_mLbTk_x3f_89_ = v___x_144_;
v_m_x3f_90_ = v___x_144_;
v_mColonEqTk_x3f_91_ = v___x_144_;
v_mVal_x3f_92_ = v___x_144_;
v_mRbTk_x3f_93_ = v___x_144_;
v___y_94_ = v_a_12_;
v___y_95_ = v_a_13_;
goto v___jp_88_;
}
v___jp_21_:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_29_, v___y_23_, v___y_32_, v___y_35_, v___y_26_, v___y_24_, v___y_22_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_39_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_37_);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
lean_inc(v_a_38_);
lean_dec_ref_known(v___x_36_, 2);
v___x_39_ = l_Lean_Fmt_fmt(v___y_27_, v___y_24_, v_a_38_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v_a_41_; lean_object* v___x_42_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
v_a_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_39_, 2);
v___x_42_ = l_Lean_Fmt_fmt(v___y_33_, v___y_24_, v_a_41_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v_a_44_; lean_object* v___x_45_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_a_43_);
v_a_44_ = lean_ctor_get(v___x_42_, 1);
lean_inc(v_a_44_);
lean_dec_ref_known(v___x_42_, 2);
v___x_45_ = l_Lean_Fmt_fmt(v___y_25_, v___y_24_, v_a_44_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v_a_47_; lean_object* v___x_48_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_46_);
v_a_47_ = lean_ctor_get(v___x_45_, 1);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_45_, 2);
v___x_48_ = l_Lean_Fmt_fmt(v___y_28_, v___y_24_, v_a_47_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_60_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_a_50_ = lean_ctor_get(v___x_48_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_60_ == 0)
{
v___x_52_ = v___x_48_;
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_60_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_20_);
v___x_55_ = lean_array_push(v___x_54_, v_a_46_);
v___x_56_ = l_Lean_Fmt_hoareTriple(v___y_34_, v___y_30_, v___y_31_, v_a_37_, v_a_40_, v_a_43_, v___x_55_, v_a_49_);
lean_dec_ref(v___x_55_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 0, v___x_56_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_a_50_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
else
{
lean_dec(v_a_46_);
lean_dec(v_a_43_);
lean_dec(v_a_40_);
lean_dec(v_a_37_);
lean_dec_ref(v___y_34_);
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_30_);
return v___x_48_;
}
}
else
{
lean_dec(v_a_43_);
lean_dec(v_a_40_);
lean_dec(v_a_37_);
lean_dec_ref(v___y_34_);
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_28_);
return v___x_45_;
}
}
else
{
lean_dec(v_a_40_);
lean_dec(v_a_37_);
lean_dec_ref(v___y_34_);
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_28_);
lean_dec(v___y_25_);
return v___x_42_;
}
}
else
{
lean_dec(v_a_37_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_28_);
lean_dec(v___y_25_);
return v___x_39_;
}
}
else
{
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_28_);
lean_dec(v___y_27_);
lean_dec(v___y_25_);
return v___x_36_;
}
}
v___jp_61_:
{
if (lean_obj_tag(v___y_65_) == 0)
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
v___y_22_ = v___y_62_;
v___y_23_ = v___y_75_;
v___y_24_ = v___y_63_;
v___y_25_ = v___y_64_;
v___y_26_ = v___y_66_;
v___y_27_ = v___y_67_;
v___y_28_ = v___y_68_;
v___y_29_ = v___y_69_;
v___y_30_ = v___y_70_;
v___y_31_ = v___y_71_;
v___y_32_ = v___y_72_;
v___y_33_ = v___y_73_;
v___y_34_ = v___y_74_;
v___y_35_ = v___x_76_;
goto v___jp_21_;
}
else
{
lean_object* v_val_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
v_val_77_ = lean_ctor_get(v___y_65_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___y_65_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___y_65_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_val_77_);
lean_dec(v___y_65_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_val_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v___y_22_ = v___y_62_;
v___y_23_ = v___y_75_;
v___y_24_ = v___y_63_;
v___y_25_ = v___y_64_;
v___y_26_ = v___y_66_;
v___y_27_ = v___y_67_;
v___y_28_ = v___y_68_;
v___y_29_ = v___y_69_;
v___y_30_ = v___y_70_;
v___y_31_ = v___y_71_;
v___y_32_ = v___y_72_;
v___y_33_ = v___y_73_;
v___y_34_ = v___y_74_;
v___y_35_ = v___x_82_;
goto v___jp_21_;
}
}
}
}
v___jp_88_:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Fmt_fmt(v_preLbTk_19_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = l_Lean_Fmt_fmt(v___x_85_, v___y_94_, v_a_98_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v_a_101_; lean_object* v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
v_a_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_99_, 2);
v___x_102_ = l_Lean_Fmt_fmt(v_preRbTk_87_, v___y_94_, v_a_101_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_postLbTk_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_postRbTk_112_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
v_a_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_102_, 2);
v___x_105_ = lean_unsigned_to_nat(4u);
v___x_106_ = l_Lean_Syntax_getArg(v_x_11_, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(5u);
v_postLbTk_108_ = l_Lean_Syntax_getArg(v_x_11_, v___x_107_);
v___x_109_ = lean_unsigned_to_nat(6u);
v___x_110_ = l_Lean_Syntax_getArg(v_x_11_, v___x_109_);
v___x_111_ = lean_unsigned_to_nat(7u);
v_postRbTk_112_ = l_Lean_Syntax_getArg(v_x_11_, v___x_111_);
lean_dec(v_x_11_);
if (lean_obj_tag(v_m_x3f_90_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_box(0);
v___y_62_ = v_a_104_;
v___y_63_ = v___y_94_;
v___y_64_ = v___x_110_;
v___y_65_ = v_mVal_x3f_92_;
v___y_66_ = v_mRbTk_x3f_93_;
v___y_67_ = v___x_106_;
v___y_68_ = v_postRbTk_112_;
v___y_69_ = v_mLbTk_x3f_89_;
v___y_70_ = v_a_100_;
v___y_71_ = v_a_103_;
v___y_72_ = v_mColonEqTk_x3f_91_;
v___y_73_ = v_postLbTk_108_;
v___y_74_ = v_a_97_;
v___y_75_ = v___x_113_;
goto v___jp_61_;
}
else
{
lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_val_114_ = lean_ctor_get(v_m_x3f_90_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v_m_x3f_90_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v_m_x3f_90_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_dec(v_m_x3f_90_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_val_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v___y_62_ = v_a_104_;
v___y_63_ = v___y_94_;
v___y_64_ = v___x_110_;
v___y_65_ = v_mVal_x3f_92_;
v___y_66_ = v_mRbTk_x3f_93_;
v___y_67_ = v___x_106_;
v___y_68_ = v_postRbTk_112_;
v___y_69_ = v_mLbTk_x3f_89_;
v___y_70_ = v_a_100_;
v___y_71_ = v_a_103_;
v___y_72_ = v_mColonEqTk_x3f_91_;
v___y_73_ = v_postLbTk_108_;
v___y_74_ = v_a_97_;
v___y_75_ = v___x_119_;
goto v___jp_61_;
}
}
}
}
else
{
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_mRbTk_x3f_93_);
lean_dec(v_mVal_x3f_92_);
lean_dec(v_mColonEqTk_x3f_91_);
lean_dec(v_m_x3f_90_);
lean_dec(v_mLbTk_x3f_89_);
lean_dec(v_x_11_);
return v___x_102_;
}
}
else
{
lean_dec(v_a_97_);
lean_dec(v_mRbTk_x3f_93_);
lean_dec(v_mVal_x3f_92_);
lean_dec(v_mColonEqTk_x3f_91_);
lean_dec(v_m_x3f_90_);
lean_dec(v_mLbTk_x3f_89_);
lean_dec(v_preRbTk_87_);
lean_dec(v_x_11_);
return v___x_99_;
}
}
else
{
lean_dec(v_mRbTk_x3f_93_);
lean_dec(v_mVal_x3f_92_);
lean_dec(v_mColonEqTk_x3f_91_);
lean_dec(v_m_x3f_90_);
lean_dec(v_mLbTk_x3f_89_);
lean_dec(v_preRbTk_87_);
lean_dec(v___x_85_);
lean_dec(v_x_11_);
return v___x_96_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleNotation___boxed(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Fmt_fmtTripleNotation(v_x_145_, v_a_146_, v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1(){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_157_ = l_Lean_Fmt_fmtAttribute;
v___x_158_ = ((lean_object*)(l_Lean_Fmt_fmtTripleNotation___closed__3));
v___x_159_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___closed__3));
v___x_160_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTripleNotation___boxed), 3, 0);
v___x_161_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_157_, v___x_158_, v___x_159_, v___x_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1___boxed(lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1();
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleExceptPost(lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_178_; lean_object* v___y_179_; lean_object* v___y_180_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v___y_184_; lean_object* v___y_185_; lean_object* v___y_186_; lean_object* v___y_187_; lean_object* v___y_188_; lean_object* v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Fmt_fmtTripleExceptPost___closed__1));
lean_inc(v_x_169_);
v___x_250_ = l_Lean_Syntax_isOfKind(v_x_169_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v_x_169_);
v___x_251_ = l_Lean_Fmt_Error_partialFormatter;
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_a_171_);
return v___x_252_;
}
else
{
lean_object* v___x_253_; lean_object* v_preLbTk_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_preRbTk_258_; lean_object* v_mLbTk_x3f_260_; lean_object* v_m_x3f_261_; lean_object* v_mColonEqTk_x3f_262_; lean_object* v_mVal_x3f_263_; lean_object* v_mRbTk_x3f_264_; lean_object* v___y_265_; lean_object* v___y_266_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v_preLbTk_254_ = l_Lean_Syntax_getArg(v_x_169_, v___x_253_);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_169_, v___x_255_);
v___x_257_ = lean_unsigned_to_nat(2u);
v_preRbTk_258_ = l_Lean_Syntax_getArg(v_x_169_, v___x_257_);
v___x_297_ = lean_unsigned_to_nat(3u);
v___x_298_ = l_Lean_Syntax_getArg(v_x_169_, v___x_297_);
v___x_299_ = l_Lean_Syntax_isNone(v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_298_);
v___x_301_ = l_Lean_Syntax_matchesNull(v___x_298_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v___x_298_);
lean_dec(v_preRbTk_258_);
lean_dec(v___x_256_);
lean_dec(v_preLbTk_254_);
lean_dec(v_x_169_);
v___x_302_ = l_Lean_Fmt_Error_partialFormatter;
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_171_);
return v___x_303_;
}
else
{
lean_object* v_m_x3f_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v_m_x3f_304_ = l_Lean_Syntax_getArg(v___x_298_, v___x_255_);
v___x_305_ = ((lean_object*)(l_Lean_Fmt_fmtTripleNotation___closed__5));
lean_inc(v_m_x3f_304_);
v___x_306_ = l_Lean_Syntax_isOfKind(v_m_x3f_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_m_x3f_304_);
lean_dec(v___x_298_);
lean_dec(v_preRbTk_258_);
lean_dec(v___x_256_);
lean_dec(v_preLbTk_254_);
lean_dec(v_x_169_);
v___x_307_ = l_Lean_Fmt_Error_partialFormatter;
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
lean_ctor_set(v___x_308_, 1, v_a_171_);
return v___x_308_;
}
else
{
lean_object* v_mLbTk_x3f_309_; lean_object* v_mColonEqTk_x3f_310_; lean_object* v_mVal_x3f_311_; lean_object* v___x_312_; lean_object* v_mRbTk_x3f_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v_mLbTk_x3f_309_ = l_Lean_Syntax_getArg(v___x_298_, v___x_253_);
v_mColonEqTk_x3f_310_ = l_Lean_Syntax_getArg(v___x_298_, v___x_257_);
v_mVal_x3f_311_ = l_Lean_Syntax_getArg(v___x_298_, v___x_297_);
v___x_312_ = lean_unsigned_to_nat(4u);
v_mRbTk_x3f_313_ = l_Lean_Syntax_getArg(v___x_298_, v___x_312_);
lean_dec(v___x_298_);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v_mLbTk_x3f_309_);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v_m_x3f_304_);
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_mColonEqTk_x3f_310_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_mVal_x3f_311_);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v_mRbTk_x3f_313_);
v_mLbTk_x3f_260_ = v___x_314_;
v_m_x3f_261_ = v___x_315_;
v_mColonEqTk_x3f_262_ = v___x_316_;
v_mVal_x3f_263_ = v___x_317_;
v_mRbTk_x3f_264_ = v___x_318_;
v___y_265_ = v_a_170_;
v___y_266_ = v_a_171_;
goto v___jp_259_;
}
}
}
else
{
lean_object* v___x_319_; 
lean_dec(v___x_298_);
v___x_319_ = lean_box(0);
v_mLbTk_x3f_260_ = v___x_319_;
v_m_x3f_261_ = v___x_319_;
v_mColonEqTk_x3f_262_ = v___x_319_;
v_mVal_x3f_263_ = v___x_319_;
v_mRbTk_x3f_264_ = v___x_319_;
v___y_265_ = v_a_170_;
v___y_266_ = v_a_171_;
goto v___jp_259_;
}
v___jp_259_:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_Fmt_fmt(v_preLbTk_254_, v___y_265_, v___y_266_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v_a_269_; lean_object* v___x_270_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc(v_a_268_);
v_a_269_ = lean_ctor_get(v___x_267_, 1);
lean_inc(v_a_269_);
lean_dec_ref_known(v___x_267_, 2);
v___x_270_ = l_Lean_Fmt_fmt(v___x_256_, v___y_265_, v_a_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_a_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
v_a_272_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_a_272_);
lean_dec_ref_known(v___x_270_, 2);
v___x_273_ = l_Lean_Fmt_fmt(v_preRbTk_258_, v___y_265_, v_a_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v_a_274_; lean_object* v_a_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_postLbTk_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v_semicolonTk_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_postRbTk_287_; 
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
v_a_275_ = lean_ctor_get(v___x_273_, 1);
lean_inc(v_a_275_);
lean_dec_ref_known(v___x_273_, 2);
v___x_276_ = lean_unsigned_to_nat(4u);
v___x_277_ = l_Lean_Syntax_getArg(v_x_169_, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(5u);
v_postLbTk_279_ = l_Lean_Syntax_getArg(v_x_169_, v___x_278_);
v___x_280_ = lean_unsigned_to_nat(6u);
v___x_281_ = l_Lean_Syntax_getArg(v_x_169_, v___x_280_);
v___x_282_ = lean_unsigned_to_nat(7u);
v_semicolonTk_283_ = l_Lean_Syntax_getArg(v_x_169_, v___x_282_);
v___x_284_ = lean_unsigned_to_nat(8u);
v___x_285_ = l_Lean_Syntax_getArg(v_x_169_, v___x_284_);
v___x_286_ = lean_unsigned_to_nat(9u);
v_postRbTk_287_ = l_Lean_Syntax_getArg(v_x_169_, v___x_286_);
lean_dec(v_x_169_);
if (lean_obj_tag(v_m_x3f_261_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
v___y_224_ = v_mRbTk_x3f_264_;
v___y_225_ = v___x_285_;
v___y_226_ = v_a_274_;
v___y_227_ = v_mColonEqTk_x3f_262_;
v___y_228_ = v_mVal_x3f_263_;
v___y_229_ = v___x_281_;
v___y_230_ = v_postRbTk_287_;
v___y_231_ = v_a_268_;
v___y_232_ = v___x_277_;
v___y_233_ = v_mLbTk_x3f_260_;
v___y_234_ = v_semicolonTk_283_;
v___y_235_ = v_a_271_;
v___y_236_ = v___y_265_;
v___y_237_ = v_a_275_;
v___y_238_ = v_postLbTk_279_;
v___y_239_ = v___x_288_;
goto v___jp_223_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_val_289_ = lean_ctor_get(v_m_x3f_261_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_m_x3f_261_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v_m_x3f_261_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_m_x3f_261_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_val_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
v___y_224_ = v_mRbTk_x3f_264_;
v___y_225_ = v___x_285_;
v___y_226_ = v_a_274_;
v___y_227_ = v_mColonEqTk_x3f_262_;
v___y_228_ = v_mVal_x3f_263_;
v___y_229_ = v___x_281_;
v___y_230_ = v_postRbTk_287_;
v___y_231_ = v_a_268_;
v___y_232_ = v___x_277_;
v___y_233_ = v_mLbTk_x3f_260_;
v___y_234_ = v_semicolonTk_283_;
v___y_235_ = v_a_271_;
v___y_236_ = v___y_265_;
v___y_237_ = v_a_275_;
v___y_238_ = v_postLbTk_279_;
v___y_239_ = v___x_294_;
goto v___jp_223_;
}
}
}
}
else
{
lean_dec(v_a_271_);
lean_dec(v_a_268_);
lean_dec(v_mRbTk_x3f_264_);
lean_dec(v_mVal_x3f_263_);
lean_dec(v_mColonEqTk_x3f_262_);
lean_dec(v_m_x3f_261_);
lean_dec(v_mLbTk_x3f_260_);
lean_dec(v_x_169_);
return v___x_273_;
}
}
else
{
lean_dec(v_a_268_);
lean_dec(v_mRbTk_x3f_264_);
lean_dec(v_mVal_x3f_263_);
lean_dec(v_mColonEqTk_x3f_262_);
lean_dec(v_m_x3f_261_);
lean_dec(v_mLbTk_x3f_260_);
lean_dec(v_preRbTk_258_);
lean_dec(v_x_169_);
return v___x_270_;
}
}
else
{
lean_dec(v_mRbTk_x3f_264_);
lean_dec(v_mVal_x3f_263_);
lean_dec(v_mColonEqTk_x3f_262_);
lean_dec(v_m_x3f_261_);
lean_dec(v_mLbTk_x3f_260_);
lean_dec(v_preRbTk_258_);
lean_dec(v___x_256_);
lean_dec(v_x_169_);
return v___x_267_;
}
}
}
v___jp_172_:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_Fmt_fmtNamedArgumentTerm_x3f(v___y_182_, v___y_173_, v___y_177_, v___y_188_, v___y_174_, v___y_185_, v___y_186_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v_a_191_; lean_object* v___x_192_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
v_a_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc(v_a_191_);
lean_dec_ref_known(v___x_189_, 2);
v___x_192_ = l_Lean_Fmt_fmt(v___y_181_, v___y_185_, v_a_191_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v_a_193_; lean_object* v_a_194_; lean_object* v___x_195_; 
v_a_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_a_193_);
v_a_194_ = lean_ctor_get(v___x_192_, 1);
lean_inc(v_a_194_);
lean_dec_ref_known(v___x_192_, 2);
v___x_195_ = l_Lean_Fmt_fmt(v___y_187_, v___y_185_, v_a_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v_a_197_; lean_object* v___x_198_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
v_a_197_ = lean_ctor_get(v___x_195_, 1);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_195_, 2);
v___x_198_ = l_Lean_Fmt_fmt(v___y_178_, v___y_185_, v_a_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_201_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
v_a_200_ = lean_ctor_get(v___x_198_, 1);
lean_inc(v_a_200_);
lean_dec_ref_known(v___x_198_, 2);
v___x_201_ = l_Lean_Fmt_fmt(v___y_183_, v___y_185_, v_a_200_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_a_202_; lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_a_202_);
v_a_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_201_, 2);
v___x_204_ = l_Lean_Fmt_fmt(v___y_175_, v___y_185_, v_a_203_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
v_a_206_ = lean_ctor_get(v___x_204_, 1);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_204_, 2);
v___x_207_ = l_Lean_Fmt_fmt(v___y_179_, v___y_185_, v_a_206_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_222_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_a_209_ = lean_ctor_get(v___x_207_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_222_ == 0)
{
v___x_211_ = v___x_207_;
v_isShared_212_ = v_isSharedCheck_222_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_222_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_213_ = lean_unsigned_to_nat(3u);
v___x_214_ = lean_mk_empty_array_with_capacity(v___x_213_);
v___x_215_ = lean_array_push(v___x_214_, v_a_199_);
v___x_216_ = lean_array_push(v___x_215_, v_a_202_);
v___x_217_ = lean_array_push(v___x_216_, v_a_205_);
v___x_218_ = l_Lean_Fmt_hoareTriple(v___y_180_, v___y_184_, v___y_176_, v_a_190_, v_a_193_, v_a_196_, v___x_217_, v_a_208_);
lean_dec_ref(v___x_217_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_218_);
v___x_220_ = v___x_211_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v_a_209_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_dec(v_a_205_);
lean_dec(v_a_202_);
lean_dec(v_a_199_);
lean_dec(v_a_196_);
lean_dec(v_a_193_);
lean_dec(v_a_190_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v___y_180_);
lean_dec_ref(v___y_176_);
return v___x_207_;
}
}
else
{
lean_dec(v_a_202_);
lean_dec(v_a_199_);
lean_dec(v_a_196_);
lean_dec(v_a_193_);
lean_dec(v_a_190_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_176_);
return v___x_204_;
}
}
else
{
lean_dec(v_a_199_);
lean_dec(v_a_196_);
lean_dec(v_a_193_);
lean_dec(v_a_190_);
lean_dec_ref(v___y_184_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
return v___x_201_;
}
}
else
{
lean_dec(v_a_196_);
lean_dec(v_a_193_);
lean_dec(v_a_190_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
return v___x_198_;
}
}
else
{
lean_dec(v_a_193_);
lean_dec(v_a_190_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
return v___x_195_;
}
}
else
{
lean_dec(v_a_190_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
return v___x_192_;
}
}
else
{
lean_dec(v___y_187_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
return v___x_189_;
}
}
v___jp_223_:
{
if (lean_obj_tag(v___y_228_) == 0)
{
lean_object* v___x_240_; 
v___x_240_ = lean_box(0);
v___y_173_ = v___y_239_;
v___y_174_ = v___y_224_;
v___y_175_ = v___y_225_;
v___y_176_ = v___y_226_;
v___y_177_ = v___y_227_;
v___y_178_ = v___y_229_;
v___y_179_ = v___y_230_;
v___y_180_ = v___y_231_;
v___y_181_ = v___y_232_;
v___y_182_ = v___y_233_;
v___y_183_ = v___y_234_;
v___y_184_ = v___y_235_;
v___y_185_ = v___y_236_;
v___y_186_ = v___y_237_;
v___y_187_ = v___y_238_;
v___y_188_ = v___x_240_;
goto v___jp_172_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
v_val_241_ = lean_ctor_get(v___y_228_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___y_228_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___y_228_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_val_241_);
lean_dec(v___y_228_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_val_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v___y_173_ = v___y_239_;
v___y_174_ = v___y_224_;
v___y_175_ = v___y_225_;
v___y_176_ = v___y_226_;
v___y_177_ = v___y_227_;
v___y_178_ = v___y_229_;
v___y_179_ = v___y_230_;
v___y_180_ = v___y_231_;
v___y_181_ = v___y_232_;
v___y_182_ = v___y_233_;
v___y_183_ = v___y_234_;
v___y_184_ = v___y_235_;
v___y_185_ = v___y_236_;
v___y_186_ = v___y_237_;
v___y_187_ = v___y_238_;
v___y_188_ = v___x_246_;
goto v___jp_172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTripleExceptPost___boxed(lean_object* v_x_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Fmt_fmtTripleExceptPost(v_x_320_, v_a_321_, v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1(){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_330_ = l_Lean_Fmt_fmtAttribute;
v___x_331_ = ((lean_object*)(l_Lean_Fmt_fmtTripleExceptPost___closed__1));
v___x_332_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___closed__1));
v___x_333_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTripleExceptPost___boxed), 3, 0);
v___x_334_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_330_, v___x_331_, v___x_332_, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1___boxed(lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1();
return v_res_336_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleNotation___regBuiltin_Lean_Fmt_fmtTripleNotation__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_WP_Triple_Basic_0__Lean_Fmt_fmtTripleExceptPost___regBuiltin_Lean_Fmt_fmtTripleExceptPost__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_WP_Triple_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_WP_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(uint8_t builtin);
lean_object* initialize_Std_WP_Triple_Basic(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_Formatters_Std_Do_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_WP_Triple_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
