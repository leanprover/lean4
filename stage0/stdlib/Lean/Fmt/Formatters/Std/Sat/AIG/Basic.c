// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Sat.AIG.Basic
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Sat.AIG.Basic import Init.Data
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtTSepArray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_tuple(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sat"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "AIG"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 9, .m_data = "term⟦_,_⟧"};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__3_value),LEAN_SCALAR_PTR_LITERAL(68, 57, 39, 164, 19, 235, 89, 113)}};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtAIGDenote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Fmt_fmtAIGDenote___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtAIGDenote"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 65, 19, 4, 82, 250, 107, 88)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 11, .m_data = "term⟦_,_,_⟧"};
static const lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__1_value),LEAN_SCALAR_PTR_LITERAL(171, 82, 193, 103, 140, 69, 25, 78)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtAIGDenote___closed__2_value),LEAN_SCALAR_PTR_LITERAL(159, 100, 232, 179, 195, 137, 50, 146)}};
static const lean_ctor_object l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 151, 104, 166, 133, 236, 24, 151)}};
static const lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "fmtAIGDenoteEntrypoint"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 99, 3, 171, 10, 234, 228, 207)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__4));
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
lean_object* v___x_18_; lean_object* v_lbTk_19_; lean_object* v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v_lbTk_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = l_Lean_Fmt_fmt(v_lbTk_19_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_commaTk_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v_fields_32_; lean_object* v___x_33_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
lean_inc(v_a_21_);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_20_, 2);
v___x_23_ = lean_unsigned_to_nat(1u);
v___x_24_ = l_Lean_Syntax_getArg(v_x_11_, v___x_23_);
v___x_25_ = lean_unsigned_to_nat(2u);
v_commaTk_26_ = l_Lean_Syntax_getArg(v_x_11_, v___x_25_);
v___x_27_ = lean_unsigned_to_nat(3u);
v___x_28_ = l_Lean_Syntax_getArg(v_x_11_, v___x_27_);
v___x_29_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_30_ = lean_array_push(v___x_29_, v___x_24_);
v___x_31_ = lean_array_push(v___x_30_, v_commaTk_26_);
v_fields_32_ = lean_array_push(v___x_31_, v___x_28_);
v___x_33_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_32_, v_a_12_, v_a_22_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_36_; lean_object* v_rbTk_37_; lean_object* v___x_38_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_33_, 2);
v___x_36_ = lean_unsigned_to_nat(4u);
v_rbTk_37_ = l_Lean_Syntax_getArg(v_x_11_, v___x_36_);
lean_dec(v_x_11_);
v___x_38_ = l_Lean_Fmt_fmt(v_rbTk_37_, v_a_12_, v_a_35_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_a_40_ = lean_ctor_get(v___x_38_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v___x_38_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_44_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__5));
v___x_45_ = l_Lean_Fmt_Layouts_tuple(v___x_44_, v_a_21_, v_a_34_, v_a_39_);
lean_dec(v_a_34_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 0, v___x_45_);
v___x_47_ = v___x_42_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_40_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_dec(v_a_34_);
lean_dec(v_a_21_);
return v___x_38_;
}
}
else
{
lean_object* v_a_50_; lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
lean_dec(v_a_21_);
lean_dec(v_x_11_);
v_a_50_ = lean_ctor_get(v___x_33_, 0);
v_a_51_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_33_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_inc(v_a_50_);
lean_dec(v___x_33_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_50_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
else
{
lean_dec(v_x_11_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenote___boxed(lean_object* v_x_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Fmt_fmtAIGDenote(v_x_59_, v_a_60_, v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1(){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = l_Lean_Fmt_fmtAttribute;
v___x_72_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__4));
v___x_73_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___closed__3));
v___x_74_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAIGDenote___boxed), 3, 0);
v___x_75_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_71_, v___x_72_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1___boxed(lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint(lean_object* v_x_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1));
lean_inc(v_x_84_);
v___x_88_ = l_Lean_Syntax_isOfKind(v_x_84_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v_x_84_);
v___x_89_ = l_Lean_Fmt_Error_partialFormatter;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_86_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; lean_object* v_lbTk_92_; lean_object* v___x_93_; 
v___x_91_ = lean_unsigned_to_nat(0u);
v_lbTk_92_ = l_Lean_Syntax_getArg(v_x_84_, v___x_91_);
v___x_93_ = l_Lean_Fmt_fmt(v_lbTk_92_, v_a_85_, v_a_86_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_a_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_comma_u2081Tk_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v_comma_u2082Tk_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_fields_111_; lean_object* v___x_112_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
v_a_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_93_, 2);
v___x_96_ = lean_unsigned_to_nat(1u);
v___x_97_ = l_Lean_Syntax_getArg(v_x_84_, v___x_96_);
v___x_98_ = lean_unsigned_to_nat(2u);
v_comma_u2081Tk_99_ = l_Lean_Syntax_getArg(v_x_84_, v___x_98_);
v___x_100_ = lean_unsigned_to_nat(3u);
v___x_101_ = l_Lean_Syntax_getArg(v_x_84_, v___x_100_);
v___x_102_ = lean_unsigned_to_nat(4u);
v_comma_u2082Tk_103_ = l_Lean_Syntax_getArg(v_x_84_, v___x_102_);
v___x_104_ = lean_unsigned_to_nat(5u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_84_, v___x_104_);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_104_);
v___x_107_ = lean_array_push(v___x_106_, v___x_97_);
v___x_108_ = lean_array_push(v___x_107_, v_comma_u2081Tk_99_);
v___x_109_ = lean_array_push(v___x_108_, v___x_101_);
v___x_110_ = lean_array_push(v___x_109_, v_comma_u2082Tk_103_);
v_fields_111_ = lean_array_push(v___x_110_, v___x_105_);
v___x_112_ = l_Lean_Fmt_fmtTSepArray___redArg(v_fields_111_, v_a_85_, v_a_95_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v_rbTk_116_; lean_object* v___x_117_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
v_a_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_112_, 2);
v___x_115_ = lean_unsigned_to_nat(6u);
v_rbTk_116_ = l_Lean_Syntax_getArg(v_x_84_, v___x_115_);
lean_dec(v_x_84_);
v___x_117_ = l_Lean_Fmt_fmt(v_rbTk_116_, v_a_85_, v_a_114_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_128_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_a_119_ = lean_ctor_get(v___x_117_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_128_ == 0)
{
v___x_121_ = v___x_117_;
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_128_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenote___closed__5));
v___x_124_ = l_Lean_Fmt_Layouts_tuple(v___x_123_, v_a_94_, v_a_113_, v_a_118_);
lean_dec(v_a_113_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_124_);
v___x_126_ = v___x_121_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_a_119_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_dec(v_a_113_);
lean_dec(v_a_94_);
return v___x_117_;
}
}
else
{
lean_object* v_a_129_; lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
lean_dec(v_a_94_);
lean_dec(v_x_84_);
v_a_129_ = lean_ctor_get(v___x_112_, 0);
v_a_130_ = lean_ctor_get(v___x_112_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_112_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_inc(v_a_129_);
lean_dec(v___x_112_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_129_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_dec(v_x_84_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Fmt_fmtAIGDenoteEntrypoint(v_x_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1(){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Fmt_fmtAttribute;
v___x_149_ = ((lean_object*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___closed__1));
v___x_150_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___closed__1));
v___x_151_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtAIGDenoteEntrypoint___boxed), 3, 0);
v___x_152_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_148_, v___x_149_, v___x_150_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1___boxed(lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
return v_res_154_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenote___regBuiltin_Lean_Fmt_fmtAIGDenote__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Sat_AIG_Basic_0__Lean_Fmt_fmtAIGDenoteEntrypoint___regBuiltin_Lean_Fmt_fmtAIGDenoteEntrypoint__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Sat_AIG_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_Basic(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Sat_AIG_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
