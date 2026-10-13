// Lean compiler output
// Module: Std.Tactic.Do.Syntax
// Imports: public import Std.Do public import Std.WP.Tactic public import Std.Tactic.Do.ProofMode public import Init.Data.Array.GetLit public import Init.Grind.Interactive
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_caseArg;
lean_object* l_Lean_mkIdent(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_binderIdent;
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_simpLemma;
extern lean_object* l_Lean_Parser_Tactic_simpErase;
extern lean_object* l_Lean_Parser_Tactic_simpStar;
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_expandMacros(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwUnsupported___redArg(lean_object*);
lean_object* l_Lean_Syntax_instReprTSyntax_repr___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_optConfig;
extern lean_object* l_Lean_Parser_Tactic_invariantAlts;
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "massumption"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 248, 144, 74, 231, 227, 47, 25)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_massumption = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mclear"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 161, 32, 25, 224, 212, 229, 174)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mclear = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_mclearError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mclearError"};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 218, 126, 93, 176, 59, 180, 45)}};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mclearError = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`mclear` expects an identifier"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mconstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mconstructor"};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 154, 195, 216, 142, 75, 110, 212)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mconstructor = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mexact"};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 11, 252, 148, 218, 54, 90)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexact = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mexactError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mexactError"};
static const lean_object* l_Lean_Parser_Tactic_mexactError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 49, 115, 16, 125, 241, 228, 129)}};
static const lean_object* l_Lean_Parser_Tactic_mexactError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexactError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexactError = (const lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`mexact` expects a term"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mexfalso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mexfalso"};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 221, 191, 226, 253, 105, 73, 187)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexfalso = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mexists"};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 170, 199, 22, 25, 76, 35, 23)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mexists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexists___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexists = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mexistsError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mexistsError"};
static const lean_object* l_Lean_Parser_Tactic_mexistsError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 62, 10, 99, 255, 118, 254, 179)}};
static const lean_object* l_Lean_Parser_Tactic_mexistsError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexistsError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexistsError = (const lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "`mexists` expects at least one term"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mframe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mframe"};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 145, 19, 234, 215, 109, 237, 186)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mframe = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mdup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mdup"};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 112, 88, 152, 42, 238, 157, 119)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mdup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mdup = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mhave"};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 47, 33, 106, 233, 48, 163, 59)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__13_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__14_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__15_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mhave = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_mhaveError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mhaveError"};
static const lean_object* l_Lean_Parser_Tactic_mhaveError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 154, 28, 196, 0, 150, 160, 162)}};
static const lean_object* l_Lean_Parser_Tactic_mhaveError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhaveError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mhaveError = (const lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "The syntax is `mhave h := term`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mreplace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mreplace"};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 100, 86, 218, 99, 164, 72, 83)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mreplace = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mreplaceError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mreplaceError"};
static const lean_object* l_Lean_Parser_Tactic_mreplaceError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(64, 153, 89, 235, 55, 53, 209, 195)}};
static const lean_object* l_Lean_Parser_Tactic_mreplaceError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplaceError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mreplaceError = (const lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "The syntax is `mreplace h := term`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mright___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mright"};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mright___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 16, 212, 5, 110, 91, 32)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mright___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mright = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mleft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mleft"};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 82, 79, 80, 116, 5, 61, 30)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mleft = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mpure"};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 40, 78, 170, 57, 132, 109, 163)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mpure = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mpureError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mpureError"};
static const lean_object* l_Lean_Parser_Tactic_mpureError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 66, 241, 214, 212, 198, 154, 78)}};
static const lean_object* l_Lean_Parser_Tactic_mpureError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpureError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mpureError = (const lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`mpure` expects an identifier"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mpureIntro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mpureIntro"};
static const lean_object* l_Lean_Parser_Tactic_mpureIntro___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 145, 131, 67, 32, 11, 101, 202)}};
static const lean_object* l_Lean_Parser_Tactic_mpureIntro___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mpureIntro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mpure_intro"};
static const lean_object* l_Lean_Parser_Tactic_mpureIntro___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mpureIntro___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpureIntro___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mpureIntro = (const lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrenameI___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mrenameI"};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 187, 19, 96, 44, 239, 241, 167)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrenameI___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mrename_i"};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mrenameI___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mrenameI___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__13;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrenameI;
static const lean_string_object l_Lean_Parser_Tactic_mrenameIError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mrenameIError"};
static const lean_object* l_Lean_Parser_Tactic_mrenameIError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 225, 118, 214, 208, 120, 62, 143)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameIError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameIError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrenameIError = (const lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`mrename_i` expects at least one identifier"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mspecialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecialize"};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 227, 189, 220, 199, 75, 123, 209)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecialize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecialize = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializeError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mspecializeError"};
static const lean_object* l_Lean_Parser_Tactic_mspecializeError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(200, 232, 171, 171, 235, 8, 139, 53)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializeError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializeError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecializeError = (const lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "The syntax is `mspecialize h term*`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mspecializePure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mspecializePure"};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 62, 145, 88, 202, 28, 127)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializePure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mspecialize_pure"};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecializePure = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializePureError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "mspecializePureError"};
static const lean_object* l_Lean_Parser_Tactic_mspecializePureError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 201, 76, 41, 194, 107, 188, 117)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePureError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePureError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecializePureError = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "The syntax is `mspecialize_pure h term*`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mstart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mstart"};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 72, 234, 250, 239, 149, 139, 165)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mstart = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mstop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mstop"};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 209, 80, 25, 253, 26, 68, 170)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mstop = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mleave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mleave"};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 47, 148, 137, 18, 118, 104, 201)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mleave = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "only"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "down_pure"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(36, 197, 222, 185, 244, 118, 88, 121)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "apply_pure"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(206, 120, 248, 21, 90, 213, 12, 16)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "entails_1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__30_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(232, 115, 74, 9, 86, 110, 89, 43)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "entails_2"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__33_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(89, 165, 111, 118, 68, 171, 3, 238)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "entails_3"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__36 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__36_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(58, 53, 5, 18, 255, 102, 81, 210)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "entails_4"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__39 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__39_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(12, 179, 224, 65, 135, 127, 28, 141)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "entails_5"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__42 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__42_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(77, 113, 174, 229, 127, 145, 206, 202)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "entails_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__45 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__45_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(212, 215, 177, 253, 123, 187, 70, 202)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "and_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__48 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__48_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(128, 230, 171, 178, 81, 245, 131, 18)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "and_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__51 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__51_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(213, 170, 166, 102, 176, 29, 41, 98)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "or_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__54 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__54_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(87, 241, 222, 128, 245, 96, 154, 86)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "or_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__57 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__57_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(225, 7, 241, 198, 168, 97, 147, 41)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__60 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__60_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(228, 34, 108, 108, 238, 250, 54, 128)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__63 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__63_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__63_value),LEAN_SCALAR_PTR_LITERAL(160, 94, 209, 202, 96, 68, 239, 91)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "imp_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__66 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__66_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(241, 115, 224, 23, 79, 216, 194, 60)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "imp_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__69 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__69_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(226, 222, 49, 108, 255, 239, 82, 221)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "iff_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__72 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__72_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(136, 129, 130, 109, 161, 68, 184, 234)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "iff_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__75 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__75_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(184, 226, 136, 56, 20, 69, 223, 188)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__78 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__78_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(20, 23, 167, 105, 240, 80, 123, 56)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "exists_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__81 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__81_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(133, 73, 133, 104, 83, 140, 176, 220)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__84 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__84_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(206, 161, 121, 29, 154, 69, 38, 192)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "forall_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__87 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__87_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__87_value),LEAN_SCALAR_PTR_LITERAL(226, 96, 144, 126, 248, 213, 74, 126)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "SVal"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "curry_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__91 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__91_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__91_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 232, 222, 117, 10, 33, 66)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "curry_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__94 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__94_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__94_value),LEAN_SCALAR_PTR_LITERAL(25, 6, 34, 146, 48, 134, 184, 12)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "uncurry_cons"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__97 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__97_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__97_value),LEAN_SCALAR_PTR_LITERAL(214, 107, 154, 238, 63, 196, 161, 227)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "uncurry_nil"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__100 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__100_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(219, 43, 211, 205, 6, 228, 81, 146)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "getThe_here"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__103 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__103_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__103_value),LEAN_SCALAR_PTR_LITERAL(253, 3, 94, 86, 219, 251, 4, 111)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "getThe_there"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__106 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__106_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(215, 208, 170, 119, 0, 201, 21, 191)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__106_value),LEAN_SCALAR_PTR_LITERAL(68, 55, 218, 34, 105, 15, 209, 114)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__110 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__110_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__111 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__111_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__110_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(27, 17, 159, 44, 239, 63, 224, 32)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "entails_true"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__114 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__114_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(246, 50, 98, 188, 214, 243, 38, 248)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "entails_false"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__117 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__117_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__109_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(130, 197, 58, 234, 180, 192, 166, 113)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ULift"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__120 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__120_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "down_ite"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__121 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__121_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(14, 162, 24, 1, 186, 170, 9, 57)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__121_value),LEAN_SCALAR_PTR_LITERAL(17, 61, 132, 74, 6, 181, 81, 222)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "down_dite"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__124 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__124_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(14, 162, 24, 1, 186, 170, 9, 57)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__124_value),LEAN_SCALAR_PTR_LITERAL(189, 251, 117, 5, 56, 9, 77, 157)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cursor"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "prefix_at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__129 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__129_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__129_value),LEAN_SCALAR_PTR_LITERAL(39, 137, 90, 168, 17, 26, 81, 55)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "suffix_at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__132 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__132_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(130, 185, 98, 39, 217, 124, 11, 73)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "current_at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__135 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__135_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__135_value),LEAN_SCALAR_PTR_LITERAL(253, 18, 249, 166, 110, 194, 192, 67)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "tail_at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__138 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__138_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__127_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(171, 26, 51, 126, 183, 221, 138, 175)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__138_value),LEAN_SCALAR_PTR_LITERAL(59, 172, 53, 183, 108, 231, 109, 39)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "and_imp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__141 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__141_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__141_value),LEAN_SCALAR_PTR_LITERAL(97, 187, 54, 56, 129, 238, 180, 43)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "and_true"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__144 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__144_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__144_value),LEAN_SCALAR_PTR_LITERAL(237, 177, 40, 201, 177, 145, 63, 28)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dite_eq_ite"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__147 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__147_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__147_value),LEAN_SCALAR_PTR_LITERAL(58, 201, 242, 159, 222, 42, 9, 203)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_prop"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__150 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__150_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__150_value),LEAN_SCALAR_PTR_LITERAL(169, 132, 191, 43, 249, 116, 95, 104)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "true_implies"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__153 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__153_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__153_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 24, 176, 31, 95, 144, 159)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__157_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__157 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__157_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__157_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__162 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__162_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mcasesPat"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 56, 213, 10, 226, 216, 228, 157)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(25, 46, 1, 143, 254, 189, 115, 160)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(mcasesPat| "};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 56, 213, 10, 226, 216, 228, 157)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mcasesPat;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mcasesPatAlts"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(236, 144, 167, 140, 164, 110, 77, 222)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat_"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 196, 52, 121, 17, 165, 127, 126)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat__;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat-"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 11, 123, 49, 91, 91, 103, 235)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "mcasesPat⟨_⟩"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 121, 122, 163, 184, 200, 40, 28)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mcasesPat(_)"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 228, 45, 90, 25, 77, 183, 251)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "mcasesPat⌜_⌝"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 36, 80, 160, 33, 204, 14, 109)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌜"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⌝"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mcasesPat□_"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 18, 113, 191, 78, 186, 91, 235)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "□"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat_u25a1__;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesPat%_"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(21, 208, 54, 86, 176, 179, 232, 169)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat_x25__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesPat#_"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 139, 158, 197, 170, 161, 118, 161)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat_x23__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Parser.Tactic.MCasesPat.clear"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__0_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Parser.Tactic.MCasesPat.one"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__3_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6;
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Parser.Tactic.MCasesPat.tuple"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__9_value;
static const lean_string_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value)}};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4;
static lean_once_cell_t l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5;
static const lean_ctor_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18_value)}};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6_value;
static const lean_ctor_object l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156_value)}};
static const lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7 = (const lean_object*)&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Parser.Tactic.MCasesPat.alts"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__11_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__12_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Parser.Tactic.MCasesPat.pure"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__14_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__15_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Parser.Tactic.MCasesPat.stateful"};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__16_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__17 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__17_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__18 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_instReprMCasesPat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_instReprMCasesPat_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instReprMCasesPat = (const lean_object*)&l_Lean_Parser_Tactic_instReprMCasesPat___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instInhabitedMCasesPat_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instInhabitedMCasesPat_default___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMCasesPat_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instInhabitedMCasesPat_default = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMCasesPat_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instInhabitedMCasesPat = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMCasesPat_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_MCasesPat_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mcases___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mcases"};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mcases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcases = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesError"};
static const lean_object* l_Lean_Parser_Tactic_mcasesError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 241, 134, 227, 96, 232, 12, 230)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesError = (const lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "The syntax is `mcases h with pat`"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mrefinePat"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 59, 126, 63, 72, 199, 165, 9)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(147, 47, 224, 199, 194, 111, 137, 195)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "`(mrefinePat| "};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 59, 126, 63, 72, 199, 165, 9)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mrefinePat;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePat_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 205, 252, 11, 203, 77, 12, 3)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat__;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePats"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 173, 91, 190, 46, 156, 169, 121)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePats = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⟨_⟩"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 110, 106, 145, 210, 7, 196)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mrefinePat(_)"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 235, 27, 55, 120, 135, 13, 209)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⌜_⌝"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 247, 138, 95, 101, 152, 141, 145)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrefinePat□_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 27, 205, 29, 81, 36, 207, 246)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1__;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat\?_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 112, 196, 176, 199, 255, 59, 175)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f__;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat%_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 246, 182, 233, 244, 232, 234, 234)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25__ = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat#_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 43, 185, 96, 20, 2, 38, 80)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat_x23__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Parser.Tactic.MRefinePat.one"};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__0_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Parser.Tactic.MRefinePat.tuple"};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Parser.Tactic.MRefinePat.pure"};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean.Parser.Tactic.MRefinePat.stateful"};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__10_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Parser.Tactic.MRefinePat.hole"};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Tactic_instReprMRefinePat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Tactic_instReprMRefinePat_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instReprMRefinePat = (const lean_object*)&l_Lean_Parser_Tactic_instReprMRefinePat___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_instInhabitedMRefinePat_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_instInhabitedMRefinePat_default___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMRefinePat_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instInhabitedMRefinePat_default = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMRefinePat_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_instInhabitedMRefinePat = (const lean_object*)&l_Lean_Parser_Tactic_instInhabitedMRefinePat_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mrefine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrefine"};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 147, 116, 116, 185, 89, 229, 87)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefine = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefineError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefineError"};
static const lean_object* l_Lean_Parser_Tactic_mrefineError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 98, 145, 116, 62, 236, 216, 113)}};
static const lean_object* l_Lean_Parser_Tactic_mrefineError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefineError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefineError = (const lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "`mrefine` expects a pattern"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mintroPat_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mintroPat"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 161, 137, 13, 29, 125, 30, 194)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 116, 95, 65, 248, 13, 22, 127)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(mintroPat| "};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 161, 137, 13, 29, 125, 30, 194)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintroPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mintroPat;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mintroPat_"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 197, 23, 48, 210, 183, 157, 165)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintroPat__ = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mintroPat∀_"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(53, 201, 27, 44, 199, 236, 234, 55)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∀"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mintroPat_u2200__;
static const lean_string_object l_Lean_Parser_Tactic_mintro___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mintro"};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 222, 62, 246, 205, 225, 8, 203)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintro = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mintroError"};
static const lean_object* l_Lean_Parser_Tactic_mintroError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 215, 98, 13, 248, 114, 226, 4)}};
static const lean_object* l_Lean_Parser_Tactic_mintroError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintroError = (const lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "`mintro` expects at least one pattern"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mrevertPat"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 192, 66, 162, 27, 20, 239, 196)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 122, 103, 47, 167, 51, 211, 55)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "`(mrevertPat| "};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 192, 66, 162, 27, 20, 239, 196)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mrevertPat;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrevertPat_"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 56, 253, 143, 81, 27, 28, 109)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat__ = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrevertPat∀_"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 101, 4, 189, 225, 175, 44, 14)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200__ = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrevert"};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 105, 168, 208, 87, 76, 255, 172)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevert = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrevertError"};
static const lean_object* l_Lean_Parser_Tactic_mrevertError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 145, 230, 122, 141, 117, 57, 209)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertError = (const lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`mrevert` expects at least one pattern"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mspecNoBind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecNoBind"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 86, 213, 46, 163, 23, 151, 189)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoBind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mspec_no_bind"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecNoBind = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecNoSimp"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 95, 246, 218, 2, 114, 192, 99)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mspec_no_simp"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecNoSimp = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Spec"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bind"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(192, 253, 214, 83, 55, 75, 153, 163)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(197, 96, 240, 111, 180, 90, 55, 33)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mspec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mspec"};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 251, 147, 100, 37, 246, 67, 31)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspec = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 66, 138, 83, 251, 171, 29, 196)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "all_goals"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "true_intro_simp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(158, 127, 133, 93, 20, 12, 235, 120)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticTrivial"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 113, 211, 1, 53, 106, 100, 38)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "tacticMvcgen_trivial_extensible"};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0_value),LEAN_SCALAR_PTR_LITERAL(126, 21, 190, 12, 230, 105, 17, 72)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "mvcgen_trivial_extensible"};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "tacticMvcgen_trivial"};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 21, 34, 5, 168, 1, 29, 164)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mvcgen_trivial"};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_vcAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcAlt"};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 45, 84, 214, 166, 18, 7, 59)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__6;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcAlt;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "vcAlts"};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 11, 218, 136, 13, 239, 233, 239)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "with "};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__10_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__12_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__14_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__16;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__19;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcAlts;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 16, 249, 94, 239, 227, 109, 158)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__3;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " ["};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__6_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__14;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__15 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__15_value)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__16 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__16_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__18;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__19;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__20;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__21;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__22;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__23;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__24;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mvcgen;
static const lean_string_object l_Lean_Parser_Tactic_mvcgenHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mvcgenHint"};
static const lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 105, 143, 226, 126, 5, 243, 226)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mvcgenHint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mvcgen\?"};
static const lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgenHint___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgenHint___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgenHint___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__6;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mvcgenHint;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(lean_object* v_x_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_68_ = ((lean_object*)(l_Lean_Parser_Tactic_mclearError___closed__1));
v___x_69_ = l_Lean_Syntax_isOfKind(v_x_65_, v___x_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_box(1);
v___x_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_a_67_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0));
v___x_73_ = l_Lean_Macro_throwError___redArg(v___x_72_, v_a_66_, v_a_67_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_a_75_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_73_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_74_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
else
{
lean_object* v_a_83_; lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_91_; 
v_a_83_ = lean_ctor_get(v___x_73_, 0);
v_a_84_ = lean_ctor_get(v___x_73_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_91_ == 0)
{
v___x_86_ = v___x_73_;
v_isShared_87_ = v_isSharedCheck_91_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_inc(v_a_83_);
lean_dec(v___x_73_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___boxed(lean_object* v_x_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(v_x_92_, v_a_93_, v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1(lean_object* v_x_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lean_Parser_Tactic_mexactError___closed__1));
v___x_154_ = l_Lean_Syntax_isOfKind(v_x_150_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_box(1);
v___x_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_a_152_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___closed__0));
v___x_158_ = l_Lean_Macro_throwError___redArg(v___x_157_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_167_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_a_160_ = lean_ctor_get(v___x_158_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_162_ = v___x_158_;
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_167_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_159_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_a_160_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
else
{
lean_object* v_a_168_; lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v_a_168_ = lean_ctor_get(v___x_158_, 0);
v_a_169_ = lean_ctor_get(v___x_158_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_158_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_inc(v_a_168_);
lean_dec(v___x_158_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_168_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___boxed(lean_object* v_x_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1(v_x_177_, v_a_178_, v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1(lean_object* v_x_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l_Lean_Parser_Tactic_mexistsError___closed__1));
v___x_238_ = l_Lean_Syntax_isOfKind(v_x_234_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_box(1);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v_a_236_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___closed__0));
v___x_242_ = l_Lean_Macro_throwError___redArg(v___x_241_, v_a_235_, v_a_236_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_a_244_ = lean_ctor_get(v___x_242_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_242_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_a_252_ = lean_ctor_get(v___x_242_, 0);
v_a_253_ = lean_ctor_get(v___x_242_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_242_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_inc(v_a_252_);
lean_dec(v___x_242_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_252_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___boxed(lean_object* v_x_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1(v_x_261_, v_a_262_, v_a_263_);
lean_dec_ref(v_a_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1(lean_object* v_x_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Parser_Tactic_mhaveError___closed__1));
v___x_370_ = l_Lean_Syntax_isOfKind(v_x_366_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_box(1);
v___x_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_a_368_);
return v___x_372_;
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___closed__0));
v___x_374_ = l_Lean_Macro_throwError___redArg(v___x_373_, v_a_367_, v_a_368_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
v_a_376_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_374_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_inc(v_a_375_);
lean_dec(v___x_374_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_375_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v___x_374_, 0);
v_a_385_ = lean_ctor_get(v___x_374_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_374_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_inc(v_a_384_);
lean_dec(v___x_374_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_384_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___boxed(lean_object* v_x_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1(v_x_393_, v_a_394_, v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1(lean_object* v_x_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Parser_Tactic_mreplaceError___closed__1));
v___x_443_ = l_Lean_Syntax_isOfKind(v_x_439_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_box(1);
v___x_445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_a_441_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___closed__0));
v___x_447_ = l_Lean_Macro_throwError___redArg(v___x_446_, v_a_440_, v_a_441_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_a_449_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_447_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_448_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_457_ = lean_ctor_get(v___x_447_, 0);
v_a_458_ = lean_ctor_get(v___x_447_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_447_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_inc(v_a_457_);
lean_dec(v___x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___boxed(lean_object* v_x_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1(v_x_466_, v_a_467_, v_a_468_);
lean_dec_ref(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1(lean_object* v_x_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureError___closed__1));
v___x_536_ = l_Lean_Syntax_isOfKind(v_x_532_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box(1);
v___x_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v_a_534_);
return v___x_538_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___closed__0));
v___x_540_ = l_Lean_Macro_throwError___redArg(v___x_539_, v_a_533_, v_a_534_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_a_542_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_540_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_541_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_550_ = lean_ctor_get(v___x_540_, 0);
v_a_551_ = lean_ctor_get(v___x_540_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_540_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_inc(v_a_550_);
lean_dec(v___x_540_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_550_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___boxed(lean_object* v_x_559_, lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1(v_x_559_, v_a_560_, v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_562_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__10(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = l_Lean_binderIdent;
v___x_601_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__9));
v___x_602_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_603_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v___x_601_);
lean_ctor_set(v___x_603_, 2, v___x_600_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__11(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__10, &l_Lean_Parser_Tactic_mrenameI___closed__10_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__10);
v___x_605_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__5));
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__12(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_607_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__11, &l_Lean_Parser_Tactic_mrenameI___closed__11_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__11);
v___x_608_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__3));
v___x_609_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_610_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_607_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__13(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__12, &l_Lean_Parser_Tactic_mrenameI___closed__12_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__12);
v___x_612_ = lean_unsigned_to_nat(1022u);
v___x_613_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__1));
v___x_614_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_611_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__13, &l_Lean_Parser_Tactic_mrenameI___closed__13_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__13);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1(lean_object* v_x_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameIError___closed__1));
v___x_632_ = l_Lean_Syntax_isOfKind(v_x_628_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(1);
v___x_634_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v_a_630_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___closed__0));
v___x_636_ = l_Lean_Macro_throwError___redArg(v___x_635_, v_a_629_, v_a_630_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_a_638_ = lean_ctor_get(v___x_636_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_636_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
v_a_646_ = lean_ctor_get(v___x_636_, 0);
v_a_647_ = lean_ctor_get(v___x_636_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_inc(v_a_646_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_646_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___boxed(lean_object* v_x_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1(v_x_655_, v_a_656_, v_a_657_);
lean_dec_ref(v_a_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecializeError___closed__1));
v___x_710_ = l_Lean_Syntax_isOfKind(v_x_706_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_box(1);
v___x_712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_a_708_);
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___closed__0));
v___x_714_ = l_Lean_Macro_throwError___redArg(v___x_713_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_a_716_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_714_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_715_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
v_a_724_ = lean_ctor_get(v___x_714_, 0);
v_a_725_ = lean_ctor_get(v___x_714_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_714_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_inc(v_a_724_);
lean_dec(v___x_714_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_724_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___boxed(lean_object* v_x_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1(v_x_733_, v_a_734_, v_a_735_);
lean_dec_ref(v_a_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1(lean_object* v_x_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecializePureError___closed__1));
v___x_784_ = l_Lean_Syntax_isOfKind(v_x_780_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_box(1);
v___x_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
lean_ctor_set(v___x_786_, 1, v_a_782_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___closed__0));
v___x_788_ = l_Lean_Macro_throwError___redArg(v___x_787_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_a_790_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_788_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_789_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_798_ = lean_ctor_get(v___x_788_, 0);
v_a_799_ = lean_ctor_get(v___x_788_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_788_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_inc(v_a_798_);
lean_dec(v___x_788_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_798_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___boxed(lean_object* v_x_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1(v_x_807_, v_a_808_, v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_810_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16(void){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Array_mkArray0___redArg();
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25));
v___x_913_ = l_Lean_mkIdent(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28));
v___x_921_ = l_Lean_mkIdent(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31));
v___x_929_ = l_Lean_mkIdent(v___x_928_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34));
v___x_937_ = l_Lean_mkIdent(v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37));
v___x_945_ = l_Lean_mkIdent(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40));
v___x_953_ = l_Lean_mkIdent(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43));
v___x_961_ = l_Lean_mkIdent(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46));
v___x_969_ = l_Lean_mkIdent(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49));
v___x_977_ = l_Lean_mkIdent(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52));
v___x_985_ = l_Lean_mkIdent(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55));
v___x_993_ = l_Lean_mkIdent(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58));
v___x_1001_ = l_Lean_mkIdent(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61));
v___x_1009_ = l_Lean_mkIdent(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64));
v___x_1017_ = l_Lean_mkIdent(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67));
v___x_1025_ = l_Lean_mkIdent(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70));
v___x_1033_ = l_Lean_mkIdent(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73));
v___x_1041_ = l_Lean_mkIdent(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76));
v___x_1049_ = l_Lean_mkIdent(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79));
v___x_1057_ = l_Lean_mkIdent(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82));
v___x_1065_ = l_Lean_mkIdent(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85));
v___x_1073_ = l_Lean_mkIdent(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88));
v___x_1081_ = l_Lean_mkIdent(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92));
v___x_1090_ = l_Lean_mkIdent(v___x_1089_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1097_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95));
v___x_1098_ = l_Lean_mkIdent(v___x_1097_);
return v___x_1098_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98));
v___x_1106_ = l_Lean_mkIdent(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101));
v___x_1114_ = l_Lean_mkIdent(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104));
v___x_1122_ = l_Lean_mkIdent(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107));
v___x_1130_ = l_Lean_mkIdent(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112));
v___x_1141_ = l_Lean_mkIdent(v___x_1140_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115));
v___x_1149_ = l_Lean_mkIdent(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118));
v___x_1157_ = l_Lean_mkIdent(v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122));
v___x_1164_ = l_Lean_mkIdent(v___x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125));
v___x_1170_ = l_Lean_mkIdent(v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130));
v___x_1179_ = l_Lean_mkIdent(v___x_1178_);
return v___x_1179_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133));
v___x_1186_ = l_Lean_mkIdent(v___x_1185_);
return v___x_1186_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136));
v___x_1193_ = l_Lean_mkIdent(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139));
v___x_1200_ = l_Lean_mkIdent(v___x_1199_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142));
v___x_1205_ = l_Lean_mkIdent(v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145));
v___x_1210_ = l_Lean_mkIdent(v___x_1209_);
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1214_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148));
v___x_1215_ = l_Lean_mkIdent(v___x_1214_);
return v___x_1215_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151));
v___x_1220_ = l_Lean_mkIdent(v___x_1219_);
return v___x_1220_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154));
v___x_1225_ = l_Lean_mkIdent(v___x_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1(lean_object* v_x_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1245_ = ((lean_object*)(l_Lean_Parser_Tactic_mleave___closed__1));
v___x_1246_ = l_Lean_Syntax_isOfKind(v_x_1242_, v___x_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1247_ = lean_box(1);
v___x_1248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
lean_ctor_set(v___x_1248_, 1, v_a_1244_);
return v___x_1248_;
}
else
{
lean_object* v_ref_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v_ref_1249_ = lean_ctor_get(v_a_1243_, 5);
v___x_1250_ = 0;
v___x_1251_ = l_Lean_SourceInfo_fromRef(v_ref_1249_, v___x_1250_);
v___x_1252_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_1253_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_1251_, 68);
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1251_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_1256_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_1257_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_1258_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_1259_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_1260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1251_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12));
v___x_1262_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13));
v___x_1263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1251_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
v___x_1264_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15));
v___x_1265_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
v___x_1266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1251_);
lean_ctor_set(v___x_1266_, 1, v___x_1257_);
lean_ctor_set(v___x_1266_, 2, v___x_1265_);
lean_inc_ref_n(v___x_1266_, 85);
v___x_1267_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1264_, v___x_1266_);
v___x_1268_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17));
v___x_1269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1251_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
v___x_1270_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1257_, v___x_1269_);
v___x_1271_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1251_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20));
v___x_1274_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26);
v___x_1275_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1274_);
v___x_1276_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_1277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1251_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29);
v___x_1279_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1278_);
v___x_1280_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32);
v___x_1281_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1280_);
v___x_1282_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35);
v___x_1283_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1282_);
v___x_1284_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38);
v___x_1285_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1284_);
v___x_1286_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41);
v___x_1287_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1286_);
v___x_1288_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44);
v___x_1289_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1288_);
v___x_1290_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47);
v___x_1291_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1290_);
v___x_1292_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50);
v___x_1293_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1292_);
v___x_1294_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53);
v___x_1295_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1294_);
v___x_1296_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56);
v___x_1297_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1296_);
v___x_1298_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59);
v___x_1299_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1298_);
v___x_1300_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62);
v___x_1301_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1300_);
v___x_1302_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65);
v___x_1303_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1302_);
v___x_1304_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68);
v___x_1305_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1304_);
v___x_1306_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71);
v___x_1307_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74);
v___x_1309_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77);
v___x_1311_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80);
v___x_1313_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83);
v___x_1315_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1314_);
v___x_1316_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86);
v___x_1317_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1316_);
v___x_1318_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89);
v___x_1319_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93);
v___x_1321_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1320_);
v___x_1322_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96);
v___x_1323_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99);
v___x_1325_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1324_);
v___x_1326_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102);
v___x_1327_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105);
v___x_1329_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108);
v___x_1331_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113);
v___x_1333_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1332_);
v___x_1334_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116);
v___x_1335_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119);
v___x_1337_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123);
v___x_1339_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126);
v___x_1341_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1340_);
v___x_1342_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131);
v___x_1343_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134);
v___x_1345_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137);
v___x_1347_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1346_);
v___x_1348_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140);
v___x_1349_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1348_);
v___x_1350_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143);
v___x_1351_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146);
v___x_1353_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149);
v___x_1355_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152);
v___x_1357_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155);
v___x_1359_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1273_, v___x_1266_, v___x_1266_, v___x_1358_);
v___x_1360_ = lean_unsigned_to_nat(83u);
v___x_1361_ = lean_mk_empty_array_with_capacity(v___x_1360_);
v___x_1362_ = lean_array_push(v___x_1361_, v___x_1275_);
lean_inc_ref_n(v___x_1277_, 40);
v___x_1363_ = lean_array_push(v___x_1362_, v___x_1277_);
v___x_1364_ = lean_array_push(v___x_1363_, v___x_1279_);
v___x_1365_ = lean_array_push(v___x_1364_, v___x_1277_);
v___x_1366_ = lean_array_push(v___x_1365_, v___x_1281_);
v___x_1367_ = lean_array_push(v___x_1366_, v___x_1277_);
v___x_1368_ = lean_array_push(v___x_1367_, v___x_1283_);
v___x_1369_ = lean_array_push(v___x_1368_, v___x_1277_);
v___x_1370_ = lean_array_push(v___x_1369_, v___x_1285_);
v___x_1371_ = lean_array_push(v___x_1370_, v___x_1277_);
v___x_1372_ = lean_array_push(v___x_1371_, v___x_1287_);
v___x_1373_ = lean_array_push(v___x_1372_, v___x_1277_);
v___x_1374_ = lean_array_push(v___x_1373_, v___x_1289_);
v___x_1375_ = lean_array_push(v___x_1374_, v___x_1277_);
v___x_1376_ = lean_array_push(v___x_1375_, v___x_1291_);
v___x_1377_ = lean_array_push(v___x_1376_, v___x_1277_);
v___x_1378_ = lean_array_push(v___x_1377_, v___x_1293_);
v___x_1379_ = lean_array_push(v___x_1378_, v___x_1277_);
v___x_1380_ = lean_array_push(v___x_1379_, v___x_1295_);
v___x_1381_ = lean_array_push(v___x_1380_, v___x_1277_);
v___x_1382_ = lean_array_push(v___x_1381_, v___x_1297_);
v___x_1383_ = lean_array_push(v___x_1382_, v___x_1277_);
v___x_1384_ = lean_array_push(v___x_1383_, v___x_1299_);
v___x_1385_ = lean_array_push(v___x_1384_, v___x_1277_);
v___x_1386_ = lean_array_push(v___x_1385_, v___x_1301_);
v___x_1387_ = lean_array_push(v___x_1386_, v___x_1277_);
v___x_1388_ = lean_array_push(v___x_1387_, v___x_1303_);
v___x_1389_ = lean_array_push(v___x_1388_, v___x_1277_);
v___x_1390_ = lean_array_push(v___x_1389_, v___x_1305_);
v___x_1391_ = lean_array_push(v___x_1390_, v___x_1277_);
v___x_1392_ = lean_array_push(v___x_1391_, v___x_1307_);
v___x_1393_ = lean_array_push(v___x_1392_, v___x_1277_);
v___x_1394_ = lean_array_push(v___x_1393_, v___x_1309_);
v___x_1395_ = lean_array_push(v___x_1394_, v___x_1277_);
v___x_1396_ = lean_array_push(v___x_1395_, v___x_1311_);
v___x_1397_ = lean_array_push(v___x_1396_, v___x_1277_);
v___x_1398_ = lean_array_push(v___x_1397_, v___x_1313_);
v___x_1399_ = lean_array_push(v___x_1398_, v___x_1277_);
v___x_1400_ = lean_array_push(v___x_1399_, v___x_1315_);
v___x_1401_ = lean_array_push(v___x_1400_, v___x_1277_);
v___x_1402_ = lean_array_push(v___x_1401_, v___x_1317_);
v___x_1403_ = lean_array_push(v___x_1402_, v___x_1277_);
v___x_1404_ = lean_array_push(v___x_1403_, v___x_1319_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1277_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1321_);
v___x_1407_ = lean_array_push(v___x_1406_, v___x_1277_);
v___x_1408_ = lean_array_push(v___x_1407_, v___x_1323_);
v___x_1409_ = lean_array_push(v___x_1408_, v___x_1277_);
v___x_1410_ = lean_array_push(v___x_1409_, v___x_1325_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1277_);
v___x_1412_ = lean_array_push(v___x_1411_, v___x_1327_);
v___x_1413_ = lean_array_push(v___x_1412_, v___x_1277_);
v___x_1414_ = lean_array_push(v___x_1413_, v___x_1329_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1277_);
v___x_1416_ = lean_array_push(v___x_1415_, v___x_1331_);
v___x_1417_ = lean_array_push(v___x_1416_, v___x_1277_);
v___x_1418_ = lean_array_push(v___x_1417_, v___x_1333_);
v___x_1419_ = lean_array_push(v___x_1418_, v___x_1277_);
v___x_1420_ = lean_array_push(v___x_1419_, v___x_1335_);
v___x_1421_ = lean_array_push(v___x_1420_, v___x_1277_);
v___x_1422_ = lean_array_push(v___x_1421_, v___x_1337_);
v___x_1423_ = lean_array_push(v___x_1422_, v___x_1277_);
v___x_1424_ = lean_array_push(v___x_1423_, v___x_1339_);
v___x_1425_ = lean_array_push(v___x_1424_, v___x_1277_);
v___x_1426_ = lean_array_push(v___x_1425_, v___x_1341_);
v___x_1427_ = lean_array_push(v___x_1426_, v___x_1277_);
v___x_1428_ = lean_array_push(v___x_1427_, v___x_1343_);
v___x_1429_ = lean_array_push(v___x_1428_, v___x_1277_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1345_);
v___x_1431_ = lean_array_push(v___x_1430_, v___x_1277_);
v___x_1432_ = lean_array_push(v___x_1431_, v___x_1347_);
v___x_1433_ = lean_array_push(v___x_1432_, v___x_1277_);
v___x_1434_ = lean_array_push(v___x_1433_, v___x_1349_);
v___x_1435_ = lean_array_push(v___x_1434_, v___x_1277_);
v___x_1436_ = lean_array_push(v___x_1435_, v___x_1351_);
v___x_1437_ = lean_array_push(v___x_1436_, v___x_1277_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1353_);
v___x_1439_ = lean_array_push(v___x_1438_, v___x_1277_);
v___x_1440_ = lean_array_push(v___x_1439_, v___x_1355_);
v___x_1441_ = lean_array_push(v___x_1440_, v___x_1277_);
v___x_1442_ = lean_array_push(v___x_1441_, v___x_1357_);
v___x_1443_ = lean_array_push(v___x_1442_, v___x_1277_);
v___x_1444_ = lean_array_push(v___x_1443_, v___x_1359_);
v___x_1445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1251_);
lean_ctor_set(v___x_1445_, 1, v___x_1257_);
lean_ctor_set(v___x_1445_, 2, v___x_1444_);
v___x_1446_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156));
v___x_1447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1251_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1257_, v___x_1272_, v___x_1445_, v___x_1447_);
v___x_1449_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158));
v___x_1450_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159));
v___x_1451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1251_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161));
v___x_1453_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__162));
v___x_1454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1251_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1452_, v___x_1454_);
v___x_1456_ = l_Lean_Syntax_node2(v___x_1251_, v___x_1449_, v___x_1451_, v___x_1455_);
v___x_1457_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1257_, v___x_1456_);
v___x_1458_ = l_Lean_Syntax_node6(v___x_1251_, v___x_1262_, v___x_1263_, v___x_1267_, v___x_1266_, v___x_1270_, v___x_1448_, v___x_1457_);
v___x_1459_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1257_, v___x_1458_);
v___x_1460_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1256_, v___x_1459_);
v___x_1461_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1255_, v___x_1460_);
v___x_1462_ = l_Lean_Syntax_node2(v___x_1251_, v___x_1258_, v___x_1260_, v___x_1461_);
v___x_1463_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1257_, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1256_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node1(v___x_1251_, v___x_1255_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1251_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = l_Lean_Syntax_node3(v___x_1251_, v___x_1252_, v___x_1254_, v___x_1465_, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v_a_1244_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___boxed(lean_object* v_x_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1(v_x_1470_, v_a_1471_, v_a_1472_);
lean_dec_ref(v_a_1471_);
return v_res_1473_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mcasesPat(void){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_box(0);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat___00__closed__2(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1538_ = l_Lean_binderIdent;
v___x_1539_ = lean_unsigned_to_nat(1022u);
v___x_1540_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
v___x_1541_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1539_);
lean_ctor_set(v___x_1541_, 2, v___x_1538_);
return v___x_1541_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat__(void){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat___00__closed__2, &l_Lean_Parser_Tactic_mcasesPat___00__closed__2_once, _init_l_Lean_Parser_Tactic_mcasesPat___00__closed__2);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4(void){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1617_ = l_Lean_binderIdent;
v___x_1618_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3));
v___x_1619_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_1620_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1619_);
lean_ctor_set(v___x_1620_, 1, v___x_1618_);
lean_ctor_set(v___x_1620_, 2, v___x_1617_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1624_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6));
v___x_1625_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4);
v___x_1626_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_1627_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v___x_1625_);
lean_ctor_set(v___x_1627_, 2, v___x_1624_);
return v___x_1627_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1628_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7);
v___x_1629_ = lean_unsigned_to_nat(1024u);
v___x_1630_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
v___x_1631_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v___x_1629_);
lean_ctor_set(v___x_1631_, 2, v___x_1628_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d(void){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1642_ = l_Lean_binderIdent;
v___x_1643_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__3));
v___x_1644_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_1645_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v___x_1643_);
lean_ctor_set(v___x_1645_, 2, v___x_1642_);
return v___x_1645_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1646_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4);
v___x_1647_ = lean_unsigned_to_nat(1022u);
v___x_1648_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
v___x_1649_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v___x_1647_);
lean_ctor_set(v___x_1649_, 2, v___x_1646_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1__(void){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5);
return v___x_1650_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = l_Lean_binderIdent;
v___x_1661_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3));
v___x_1662_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_1663_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
lean_ctor_set(v___x_1663_, 2, v___x_1660_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4);
v___x_1665_ = lean_unsigned_to_nat(1022u);
v___x_1666_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1));
v___x_1667_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v___x_1665_);
lean_ctor_set(v___x_1667_, 2, v___x_1664_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25__(void){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1(lean_object* v_x_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1));
lean_inc(v_x_1669_);
v___x_1673_ = l_Lean_Syntax_isOfKind(v_x_1669_, v___x_1672_);
if (v___x_1673_ == 0)
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v_x_1669_);
v___x_1674_ = lean_box(1);
v___x_1675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
lean_ctor_set(v___x_1675_, 1, v_a_1671_);
return v___x_1675_;
}
else
{
lean_object* v_ref_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_ref_1676_ = lean_ctor_get(v_a_1670_, 5);
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = l_Lean_Syntax_getArg(v_x_1669_, v___x_1677_);
lean_dec(v_x_1669_);
v___x_1679_ = 0;
v___x_1680_ = l_Lean_SourceInfo_fromRef(v_ref_1676_, v___x_1679_);
v___x_1681_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
v___x_1682_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2));
lean_inc_n(v___x_1680_, 2);
v___x_1683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1680_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5));
v___x_1685_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1680_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_node3(v___x_1680_, v___x_1681_, v___x_1683_, v___x_1678_, v___x_1685_);
v___x_1687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_a_1671_);
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1___boxed(lean_object* v_x_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1(v_x_1688_, v_a_1689_, v_a_1690_);
lean_dec_ref(v_a_1689_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4(void){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1701_ = l_Lean_binderIdent;
v___x_1702_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__3));
v___x_1703_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_1704_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
lean_ctor_set(v___x_1704_, 1, v___x_1702_);
lean_ctor_set(v___x_1704_, 2, v___x_1701_);
return v___x_1704_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1705_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4);
v___x_1706_ = lean_unsigned_to_nat(1022u);
v___x_1707_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1));
v___x_1708_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1705_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23__(void){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1(lean_object* v_x_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1));
lean_inc(v_x_1710_);
v___x_1714_ = l_Lean_Syntax_isOfKind(v_x_1710_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec(v_x_1710_);
v___x_1715_ = lean_box(1);
v___x_1716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v_a_1712_);
return v___x_1716_;
}
else
{
lean_object* v_ref_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_ref_1717_ = lean_ctor_get(v_a_1711_, 5);
v___x_1718_ = lean_unsigned_to_nat(1u);
v___x_1719_ = l_Lean_Syntax_getArg(v_x_1710_, v___x_1718_);
lean_dec(v_x_1710_);
v___x_1720_ = 0;
v___x_1721_ = l_Lean_SourceInfo_fromRef(v_ref_1717_, v___x_1720_);
v___x_1722_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
v___x_1723_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2));
lean_inc(v___x_1721_);
v___x_1724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1721_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Lean_Syntax_node2(v___x_1721_, v___x_1722_, v___x_1724_, v___x_1719_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1712_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1___boxed(lean_object* v_x_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1(v_x_1727_, v_a_1728_, v_a_1729_);
lean_dec_ref(v_a_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___impl(lean_object* v_x_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_obj_tag_nat(v_x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___impl___boxed(lean_object* v_x_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Parser_Tactic_MCasesPat_ctorIdx___impl(v_x_1733_);
lean_dec(v_x_1733_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(lean_object* v_t_1735_, lean_object* v_k_1736_){
_start:
{
if (lean_obj_tag(v_t_1735_) == 1)
{
return v_k_1736_;
}
else
{
lean_object* v_name_1737_; lean_object* v___x_1738_; 
v_name_1737_ = lean_ctor_get(v_t_1735_, 0);
lean_inc(v_name_1737_);
lean_dec(v_t_1735_);
v___x_1738_ = lean_apply_1(v_k_1736_, v_name_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim(lean_object* v_motive__1_1739_, lean_object* v_ctorIdx_1740_, lean_object* v_t_1741_, lean_object* v_h_1742_, lean_object* v_k_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1741_, v_k_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___boxed(lean_object* v_motive__1_1745_, lean_object* v_ctorIdx_1746_, lean_object* v_t_1747_, lean_object* v_h_1748_, lean_object* v_k_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim(v_motive__1_1745_, v_ctorIdx_1746_, v_t_1747_, v_h_1748_, v_k_1749_);
lean_dec(v_ctorIdx_1746_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim___redArg(lean_object* v_t_1751_, lean_object* v_one_1752_){
_start:
{
lean_object* v___x_1753_; 
v___x_1753_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1751_, v_one_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim(lean_object* v_motive__1_1754_, lean_object* v_t_1755_, lean_object* v_h_1756_, lean_object* v_one_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1755_, v_one_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim___redArg(lean_object* v_t_1759_, lean_object* v_clear_1760_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1759_, v_clear_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim(lean_object* v_motive__1_1762_, lean_object* v_t_1763_, lean_object* v_h_1764_, lean_object* v_clear_1765_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1763_, v_clear_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim___redArg(lean_object* v_t_1767_, lean_object* v_tuple_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1767_, v_tuple_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim(lean_object* v_motive__1_1770_, lean_object* v_t_1771_, lean_object* v_h_1772_, lean_object* v_tuple_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1771_, v_tuple_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim___redArg(lean_object* v_t_1775_, lean_object* v_alts_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1775_, v_alts_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim(lean_object* v_motive__1_1778_, lean_object* v_t_1779_, lean_object* v_h_1780_, lean_object* v_alts_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1779_, v_alts_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim___redArg(lean_object* v_t_1783_, lean_object* v_pure_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1783_, v_pure_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim(lean_object* v_motive__1_1786_, lean_object* v_t_1787_, lean_object* v_h_1788_, lean_object* v_pure_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1787_, v_pure_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim___redArg(lean_object* v_t_1791_, lean_object* v_stateful_1792_){
_start:
{
lean_object* v___x_1793_; 
v___x_1793_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1791_, v_stateful_1792_);
return v___x_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim(lean_object* v_motive__1_1794_, lean_object* v_t_1795_, lean_object* v_h_1796_, lean_object* v_stateful_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1795_, v_stateful_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_unsigned_to_nat(2u);
v___x_1809_ = lean_nat_to_int(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6(void){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = lean_nat_to_int(v___x_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
lean_dec(v_x_1826_);
return v_x_1827_;
}
else
{
lean_object* v_head_1829_; lean_object* v_tail_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1841_; 
v_head_1829_ = lean_ctor_get(v_x_1828_, 0);
v_tail_1830_ = lean_ctor_get(v_x_1828_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_x_1828_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1832_ = v_x_1828_;
v_isShared_1833_ = v_isSharedCheck_1841_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tail_1830_);
lean_inc(v_head_1829_);
lean_dec(v_x_1828_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1841_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
lean_inc(v_x_1826_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 5);
lean_ctor_set(v___x_1832_, 1, v_x_1826_);
lean_ctor_set(v___x_1832_, 0, v_x_1827_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_x_1827_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_x_1826_);
v___x_1835_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1836_ = lean_unsigned_to_nat(0u);
v___x_1837_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_head_1829_, v___x_1836_);
v___x_1838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v_x_1827_ = v___x_1838_;
v_x_1828_ = v_tail_1830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1(lean_object* v_x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1844_) == 0)
{
lean_dec(v_x_1842_);
return v_x_1843_;
}
else
{
lean_object* v_head_1845_; lean_object* v_tail_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1857_; 
v_head_1845_ = lean_ctor_get(v_x_1844_, 0);
v_tail_1846_ = lean_ctor_get(v_x_1844_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_x_1844_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1848_ = v_x_1844_;
v_isShared_1849_ = v_isSharedCheck_1857_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_tail_1846_);
lean_inc(v_head_1845_);
lean_dec(v_x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1857_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
lean_inc(v_x_1842_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 5);
lean_ctor_set(v___x_1848_, 1, v_x_1842_);
lean_ctor_set(v___x_1848_, 0, v_x_1843_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_x_1843_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_x_1842_);
v___x_1851_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_head_1845_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1_spec__3(v_x_1842_, v___x_1854_, v_tail_1846_);
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0(lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v___x_1860_; 
lean_dec(v_x_1859_);
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
else
{
lean_object* v_tail_1861_; 
v_tail_1861_ = lean_ctor_get(v_x_1858_, 1);
if (lean_obj_tag(v_tail_1861_) == 0)
{
lean_object* v_head_1862_; lean_object* v___x_1863_; 
lean_dec(v_x_1859_);
v_head_1862_ = lean_ctor_get(v_x_1858_, 0);
lean_inc(v_head_1862_);
lean_dec_ref_known(v_x_1858_, 2);
v___x_1863_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(v_head_1862_);
return v___x_1863_;
}
else
{
lean_object* v_head_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_inc(v_tail_1861_);
v_head_1864_ = lean_ctor_get(v_x_1858_, 0);
lean_inc(v_head_1864_);
lean_dec_ref_known(v_x_1858_, 2);
v___x_1865_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(v_head_1864_);
v___x_1866_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1(v_x_1859_, v___x_1865_, v_tail_1861_);
return v___x_1866_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_1868_ = lean_string_length(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4);
v___x_1870_ = lean_nat_to_int(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(lean_object* v_a_1875_){
_start:
{
if (lean_obj_tag(v_a_1875_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1));
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1877_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3));
v___x_1878_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0(v_a_1875_, v___x_1877_);
v___x_1879_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5);
v___x_1880_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6));
v___x_1881_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v___x_1878_);
v___x_1882_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7));
v___x_1883_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1879_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = 0;
v___x_1886_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set_uint8(v___x_1886_, sizeof(void*)*1, v___x_1885_);
return v___x_1886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr(lean_object* v_x_1905_, lean_object* v_prec_1906_){
_start:
{
lean_object* v___y_1908_; 
switch(lean_obj_tag(v_x_1905_))
{
case 0:
{
lean_object* v_name_1914_; lean_object* v___y_1916_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_name_1914_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_name_1914_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1924_ = lean_unsigned_to_nat(1024u);
v___x_1925_ = lean_nat_dec_le(v___x_1924_, v_prec_1906_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1916_ = v___x_1926_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1916_ = v___x_1927_;
goto v___jp_1915_;
}
v___jp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1917_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__4));
v___x_1918_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_1914_);
v___x_1919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
lean_inc(v___y_1916_);
v___x_1920_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___y_1916_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = 0;
v___x_1922_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*1, v___x_1921_);
v___x_1923_ = l_Repr_addAppParen(v___x_1922_, v_prec_1906_);
return v___x_1923_;
}
}
case 1:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_unsigned_to_nat(1024u);
v___x_1929_ = lean_nat_dec_le(v___x_1928_, v_prec_1906_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1908_ = v___x_1930_;
goto v___jp_1907_;
}
else
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1908_ = v___x_1931_;
goto v___jp_1907_;
}
}
case 2:
{
lean_object* v_args_1932_; lean_object* v___y_1934_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_args_1932_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_args_1932_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1942_ = lean_unsigned_to_nat(1024u);
v___x_1943_ = lean_nat_dec_le(v___x_1942_, v_prec_1906_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1934_ = v___x_1944_;
goto v___jp_1933_;
}
else
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1934_ = v___x_1945_;
goto v___jp_1933_;
}
v___jp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1935_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__9));
v___x_1936_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_args_1932_);
v___x_1937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
lean_inc(v___y_1934_);
v___x_1938_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___y_1934_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = 0;
v___x_1940_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set_uint8(v___x_1940_, sizeof(void*)*1, v___x_1939_);
v___x_1941_ = l_Repr_addAppParen(v___x_1940_, v_prec_1906_);
return v___x_1941_;
}
}
case 3:
{
lean_object* v_args_1946_; lean_object* v___y_1948_; lean_object* v___x_1956_; uint8_t v___x_1957_; 
v_args_1946_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_args_1946_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1956_ = lean_unsigned_to_nat(1024u);
v___x_1957_ = lean_nat_dec_le(v___x_1956_, v_prec_1906_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1948_ = v___x_1958_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1959_; 
v___x_1959_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1948_ = v___x_1959_;
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v___x_1949_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__12));
v___x_1950_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_args_1946_);
v___x_1951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
lean_inc(v___y_1948_);
v___x_1952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___y_1948_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = 0;
v___x_1954_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*1, v___x_1953_);
v___x_1955_ = l_Repr_addAppParen(v___x_1954_, v_prec_1906_);
return v___x_1955_;
}
}
case 4:
{
lean_object* v_h_1960_; lean_object* v___y_1962_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_h_1960_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_h_1960_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1970_ = lean_unsigned_to_nat(1024u);
v___x_1971_ = lean_nat_dec_le(v___x_1970_, v_prec_1906_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1962_ = v___x_1972_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1973_; 
v___x_1973_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1962_ = v___x_1973_;
goto v___jp_1961_;
}
v___jp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1963_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__15));
v___x_1964_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_1960_);
v___x_1965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
lean_inc(v___y_1962_);
v___x_1966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___y_1962_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = 0;
v___x_1968_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*1, v___x_1967_);
v___x_1969_ = l_Repr_addAppParen(v___x_1968_, v_prec_1906_);
return v___x_1969_;
}
}
default: 
{
lean_object* v_h_1974_; lean_object* v___y_1976_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_h_1974_ = lean_ctor_get(v_x_1905_, 0);
lean_inc(v_h_1974_);
lean_dec_ref_known(v_x_1905_, 1);
v___x_1984_ = lean_unsigned_to_nat(1024u);
v___x_1985_ = lean_nat_dec_le(v___x_1984_, v_prec_1906_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1976_ = v___x_1986_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1976_ = v___x_1987_;
goto v___jp_1975_;
}
v___jp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; uint8_t v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__18));
v___x_1978_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_1974_);
v___x_1979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
lean_inc(v___y_1976_);
v___x_1980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1976_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = 0;
v___x_1982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set_uint8(v___x_1982_, sizeof(void*)*1, v___x_1981_);
v___x_1983_ = l_Repr_addAppParen(v___x_1982_, v_prec_1906_);
return v___x_1983_;
}
}
}
v___jp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1909_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__1));
lean_inc(v___y_1908_);
v___x_1910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___y_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = 0;
v___x_1912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set_uint8(v___x_1912_, sizeof(void*)*1, v___x_1911_);
v___x_1913_ = l_Repr_addAppParen(v___x_1912_, v_prec_1906_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v___y_1988_, v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___boxed(lean_object* v_x_1991_, lean_object* v_prec_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_x_1991_, v_prec_1992_);
lean_dec(v_prec_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__1(lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_nat_to_int(v_a_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0(lean_object* v_a_1996_, lean_object* v_n_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_a_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___boxed(lean_object* v_a_1999_, lean_object* v_n_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0(v_a_1999_, v_n_2000_);
lean_dec(v_n_2000_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(uint8_t v___x_2008_, uint8_t v___x_2009_, lean_object* v_as_2010_, size_t v_i_2011_, size_t v_stop_2012_, lean_object* v_b_2013_){
_start:
{
lean_object* v___y_2015_; uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_eq(v_i_2011_, v_stop_2012_);
if (v___x_2019_ == 0)
{
lean_object* v_fst_2020_; uint8_t v___x_2021_; 
v_fst_2020_ = lean_ctor_get(v_b_2013_, 0);
v___x_2021_ = lean_unbox(v_fst_2020_);
if (v___x_2021_ == 0)
{
lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2030_; 
v_snd_2022_ = lean_ctor_get(v_b_2013_, 1);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v_b_2013_, 0);
lean_dec(v_unused_2031_);
v___x_2024_ = v_b_2013_;
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_dec(v_b_2013_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2030_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_box(v___x_2008_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2026_);
v___x_2028_ = v___x_2024_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_snd_2022_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v___y_2015_ = v___x_2028_;
goto v___jp_2014_;
}
}
}
else
{
lean_object* v_snd_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_snd_2032_ = lean_ctor_get(v_b_2013_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v_b_2013_, 0);
lean_dec(v_unused_2043_);
v___x_2034_ = v_b_2013_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snd_2032_);
lean_dec(v_b_2013_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = lean_array_uget_borrowed(v_as_2010_, v_i_2011_);
lean_inc(v___x_2036_);
v___x_2037_ = lean_array_push(v_snd_2032_, v___x_2036_);
v___x_2038_ = lean_box(v___x_2009_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 1, v___x_2037_);
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2037_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v___y_2015_ = v___x_2040_;
goto v___jp_2014_;
}
}
}
}
else
{
return v_b_2013_;
}
v___jp_2014_:
{
size_t v___x_2016_; size_t v___x_2017_; 
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_2011_, v___x_2016_);
v_i_2011_ = v___x_2017_;
v_b_2013_ = v___y_2015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2___boxed(lean_object* v___x_2044_, lean_object* v___x_2045_, lean_object* v_as_2046_, lean_object* v_i_2047_, lean_object* v_stop_2048_, lean_object* v_b_2049_){
_start:
{
uint8_t v___x_947__boxed_2050_; uint8_t v___x_948__boxed_2051_; size_t v_i_boxed_2052_; size_t v_stop_boxed_2053_; lean_object* v_res_2054_; 
v___x_947__boxed_2050_ = lean_unbox(v___x_2044_);
v___x_948__boxed_2051_ = lean_unbox(v___x_2045_);
v_i_boxed_2052_ = lean_unbox_usize(v_i_2047_);
lean_dec(v_i_2047_);
v_stop_boxed_2053_ = lean_unbox_usize(v_stop_2048_);
lean_dec(v_stop_2048_);
v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_947__boxed_2050_, v___x_948__boxed_2051_, v_as_2046_, v_i_boxed_2052_, v_stop_boxed_2053_, v_b_2049_);
lean_dec_ref(v_as_2046_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(size_t v_sz_2055_, size_t v_i_2056_, lean_object* v_bs_2057_){
_start:
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_usize_dec_lt(v_i_2056_, v_sz_2055_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; 
v___x_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2059_, 0, v_bs_2057_);
return v___x_2059_;
}
else
{
lean_object* v_v_2060_; lean_object* v___x_2061_; lean_object* v_bs_x27_2062_; size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v_v_2060_ = lean_array_uget(v_bs_2057_, v_i_2056_);
v___x_2061_ = lean_unsigned_to_nat(0u);
v_bs_x27_2062_ = lean_array_uset(v_bs_2057_, v_i_2056_, v___x_2061_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2056_, v___x_2063_);
v___x_2065_ = lean_array_uset(v_bs_x27_2062_, v_i_2056_, v_v_2060_);
v_i_2056_ = v___x_2064_;
v_bs_2057_ = v___x_2065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0___boxed(lean_object* v_sz_2067_, lean_object* v_i_2068_, lean_object* v_bs_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2067_);
lean_dec(v_sz_2067_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2068_);
lean_dec(v_i_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(v_sz_boxed_2070_, v_i_boxed_2071_, v_bs_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go(lean_object* v_a_2081_){
_start:
{
lean_object* v___y_2083_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
lean_inc(v_a_2081_);
v___x_2109_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2108_);
if (v___x_2109_ == 0)
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1));
lean_inc(v_a_2081_);
v___x_2111_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1));
lean_inc(v_a_2081_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; uint8_t v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
lean_inc(v_a_2081_);
v___x_2115_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2114_);
if (v___x_2115_ == 0)
{
lean_object* v___x_2116_; uint8_t v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
lean_inc(v_a_2081_);
v___x_2117_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2116_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1));
lean_inc(v_a_2081_);
v___x_2119_ = l_Lean_Syntax_isOfKind(v_a_2081_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; 
lean_dec(v_a_2081_);
v___x_2120_ = lean_box(0);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; lean_object* v_pat_2122_; lean_object* v___x_2123_; 
v___x_2121_ = lean_unsigned_to_nat(1u);
v_pat_2122_ = l_Lean_Syntax_getArg(v_a_2081_, v___x_2121_);
lean_dec(v_a_2081_);
v___x_2123_ = l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(v_pat_2122_);
return v___x_2123_;
}
}
else
{
lean_object* v___x_2124_; lean_object* v_h_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_unsigned_to_nat(1u);
v_h_2125_ = l_Lean_Syntax_getArg(v_a_2081_, v___x_2124_);
lean_dec(v_a_2081_);
v___x_2126_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2126_, 0, v_h_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
return v___x_2127_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v_h_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = lean_unsigned_to_nat(1u);
v_h_2129_ = l_Lean_Syntax_getArg(v_a_2081_, v___x_2128_);
lean_dec(v_a_2081_);
v___x_2130_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_h_2129_);
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
return v___x_2131_;
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2132_ = lean_unsigned_to_nat(1u);
v___x_2133_ = l_Lean_Syntax_getArg(v_a_2081_, v___x_2132_);
lean_dec(v_a_2081_);
v___x_2134_ = l_Lean_Syntax_getArgs(v___x_2133_);
lean_dec(v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___x_2137_ = lean_array_get_size(v___x_2134_);
v___x_2138_ = lean_nat_dec_lt(v___x_2135_, v___x_2137_);
if (v___x_2138_ == 0)
{
lean_dec_ref(v___x_2134_);
v___y_2083_ = v___x_2136_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; lean_object* v_snd_2144_; 
v___x_2139_ = lean_box(v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___x_2136_);
v___x_2141_ = ((size_t)0ULL);
v___x_2142_ = lean_usize_of_nat(v___x_2137_);
v___x_2143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2113_, v___x_2111_, v___x_2134_, v___x_2141_, v___x_2142_, v___x_2140_);
lean_dec_ref(v___x_2134_);
v_snd_2144_ = lean_ctor_get(v___x_2143_, 1);
lean_inc(v_snd_2144_);
lean_dec_ref(v___x_2143_);
v___y_2083_ = v_snd_2144_;
goto v___jp_2082_;
}
}
}
else
{
lean_object* v___x_2145_; 
lean_dec(v_a_2081_);
v___x_2145_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1));
return v___x_2145_;
}
}
else
{
lean_object* v___x_2146_; lean_object* v_name_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v_name_2147_ = l_Lean_Syntax_getArg(v_a_2081_, v___x_2146_);
lean_dec(v_a_2081_);
v___x_2148_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2147_);
v___x_2149_ = l_Lean_Syntax_isOfKind(v_name_2147_, v___x_2148_);
if (v___x_2149_ == 0)
{
lean_object* v___x_2150_; 
lean_dec(v_name_2147_);
v___x_2150_ = lean_box(0);
return v___x_2150_;
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_name_2147_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
v___jp_2082_:
{
size_t v_sz_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v_sz_2084_ = lean_array_size(v___y_2083_);
v___x_2085_ = ((size_t)0ULL);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(v_sz_2084_, v___x_2085_, v___y_2083_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_box(0);
return v___x_2087_;
}
else
{
lean_object* v_val_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2107_; 
v_val_2088_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2107_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_val_2088_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2107_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
size_t v_sz_2092_; lean_object* v___x_2093_; 
v_sz_2092_ = lean_array_size(v_val_2088_);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(v_sz_2092_, v___x_2085_, v_val_2088_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2094_; 
lean_del_object(v___x_2090_);
v___x_2094_ = lean_box(0);
return v___x_2094_;
}
else
{
lean_object* v_val_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2106_; 
v_val_2095_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2097_ = v___x_2093_;
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_val_2095_);
lean_dec(v___x_2093_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2106_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_array_to_list(v_val_2095_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 2);
lean_ctor_set(v___x_2090_, 0, v___x_2099_);
v___x_2101_ = v___x_2090_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2101_);
v___x_2103_ = v___x_2097_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(size_t v_sz_2153_, size_t v_i_2154_, lean_object* v_bs_2155_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_usize_dec_lt(v_i_2154_, v_sz_2153_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_bs_2155_);
return v___x_2157_;
}
else
{
lean_object* v_v_2158_; lean_object* v___x_2159_; 
v_v_2158_ = lean_array_uget_borrowed(v_bs_2155_, v_i_2154_);
lean_inc(v_v_2158_);
v___x_2159_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_v_2158_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v___x_2160_; 
lean_dec_ref(v_bs_2155_);
v___x_2160_ = lean_box(0);
return v___x_2160_;
}
else
{
lean_object* v_val_2161_; lean_object* v___x_2162_; lean_object* v_bs_x27_2163_; size_t v___x_2164_; size_t v___x_2165_; lean_object* v___x_2166_; 
v_val_2161_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_val_2161_);
lean_dec_ref_known(v___x_2159_, 1);
v___x_2162_ = lean_unsigned_to_nat(0u);
v_bs_x27_2163_ = lean_array_uset(v_bs_2155_, v_i_2154_, v___x_2162_);
v___x_2164_ = ((size_t)1ULL);
v___x_2165_ = lean_usize_add(v_i_2154_, v___x_2164_);
v___x_2166_ = lean_array_uset(v_bs_x27_2163_, v_i_2154_, v_val_2161_);
v_i_2154_ = v___x_2165_;
v_bs_2155_ = v___x_2166_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(lean_object* v_a_2168_){
_start:
{
lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2169_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__1));
lean_inc(v_a_2168_);
v___x_2170_ = l_Lean_Syntax_isOfKind(v_a_2168_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_dec(v_a_2168_);
v___x_2171_ = lean_box(0);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_args_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = l_Lean_Syntax_getArg(v_a_2168_, v___x_2172_);
lean_dec(v_a_2168_);
v_args_2174_ = l_Lean_Syntax_getArgs(v___x_2173_);
lean_dec(v___x_2173_);
v___x_2175_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2174_);
lean_dec_ref(v_args_2174_);
v___x_2176_ = lean_array_get_size(v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_nat_dec_eq(v___x_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
size_t v_sz_2179_; size_t v___x_2180_; lean_object* v___x_2181_; 
v_sz_2179_ = lean_array_size(v___x_2175_);
v___x_2180_ = ((size_t)0ULL);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_2179_, v___x_2180_, v___x_2175_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_box(0);
return v___x_2182_;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2192_; 
v_val_2183_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2185_ = v___x_2181_;
v_isShared_2186_ = v_isSharedCheck_2192_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_val_2183_);
lean_dec(v___x_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2192_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2187_ = lean_array_to_list(v_val_2183_);
v___x_2188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 0, v___x_2188_);
v___x_2190_ = v___x_2185_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_array_fget(v___x_2175_, v___x_2172_);
lean_dec_ref(v___x_2175_);
v___x_2194_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v___x_2193_);
return v___x_2194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(size_t v_sz_2195_, size_t v_i_2196_, lean_object* v_bs_2197_){
_start:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_usize_dec_lt(v_i_2196_, v_sz_2195_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v_bs_2197_);
return v___x_2199_;
}
else
{
lean_object* v_v_2200_; lean_object* v___x_2201_; 
v_v_2200_ = lean_array_uget_borrowed(v_bs_2197_, v_i_2196_);
lean_inc(v_v_2200_);
v___x_2201_ = l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(v_v_2200_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v___x_2202_; 
lean_dec_ref(v_bs_2197_);
v___x_2202_ = lean_box(0);
return v___x_2202_;
}
else
{
lean_object* v_val_2203_; lean_object* v___x_2204_; lean_object* v_bs_x27_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v_val_2203_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2204_ = lean_unsigned_to_nat(0u);
v_bs_x27_2205_ = lean_array_uset(v_bs_2197_, v_i_2196_, v___x_2204_);
v___x_2206_ = ((size_t)1ULL);
v___x_2207_ = lean_usize_add(v_i_2196_, v___x_2206_);
v___x_2208_ = lean_array_uset(v_bs_x27_2205_, v_i_2196_, v_val_2203_);
v_i_2196_ = v___x_2207_;
v_bs_2197_ = v___x_2208_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1___boxed(lean_object* v_sz_2210_, lean_object* v_i_2211_, lean_object* v_bs_2212_){
_start:
{
size_t v_sz_boxed_2213_; size_t v_i_boxed_2214_; lean_object* v_res_2215_; 
v_sz_boxed_2213_ = lean_unbox_usize(v_sz_2210_);
lean_dec(v_sz_2210_);
v_i_boxed_2214_ = lean_unbox_usize(v_i_2211_);
lean_dec(v_i_2211_);
v_res_2215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(v_sz_boxed_2213_, v_i_boxed_2214_, v_bs_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4___boxed(lean_object* v_sz_2216_, lean_object* v_i_2217_, lean_object* v_bs_2218_){
_start:
{
size_t v_sz_boxed_2219_; size_t v_i_boxed_2220_; lean_object* v_res_2221_; 
v_sz_boxed_2219_ = lean_unbox_usize(v_sz_2216_);
lean_dec(v_sz_2216_);
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_boxed_2219_, v_i_boxed_2220_, v_bs_2218_);
return v_res_2221_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(lean_object* v_k_2228_){
_start:
{
lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2229_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1));
v___x_2230_ = lean_name_eq(v_k_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
uint8_t v___x_2231_; 
v___x_2231_ = 1;
return v___x_2231_;
}
else
{
uint8_t v___x_2232_; 
v___x_2232_ = 0;
return v___x_2232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___boxed(lean_object* v_k_2233_){
_start:
{
uint8_t v_res_2234_; lean_object* v_r_2235_; 
v_res_2234_ = l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(v_k_2233_);
lean_dec(v_k_2233_);
v_r_2235_ = lean_box(v_res_2234_);
return v_r_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse(lean_object* v_pat_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_){
_start:
{
lean_object* v___f_2240_; lean_object* v___x_2241_; 
v___f_2240_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2238_);
v___x_2241_ = l_Lean_expandMacros(v_pat_2237_, v___f_2240_, v_a_2238_, v_a_2239_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v_a_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2253_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_a_2243_ = lean_ctor_get(v___x_2241_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2245_ = v___x_2241_;
v_isShared_2246_ = v_isSharedCheck_2253_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_a_2243_);
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2253_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_a_2242_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
lean_del_object(v___x_2245_);
v___x_2248_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2243_);
return v___x_2248_;
}
else
{
lean_object* v_val_2249_; lean_object* v___x_2251_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_val_2249_);
lean_dec_ref_known(v___x_2247_, 1);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v_val_2249_);
v___x_2251_ = v___x_2245_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_val_2249_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_a_2243_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
v_a_2254_ = lean_ctor_get(v___x_2241_, 0);
v_a_2255_ = lean_ctor_get(v___x_2241_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2241_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_inc(v_a_2254_);
lean_dec(v___x_2241_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2254_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object* v_pat_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_Parser_Tactic_MCasesPat_parse(v_pat_2263_, v_a_2264_, v_a_2265_);
lean_dec_ref(v_a_2264_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(lean_object* v_x_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2311_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesError___closed__1));
v___x_2312_ = l_Lean_Syntax_isOfKind(v_x_2308_, v___x_2311_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_box(1);
v___x_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v_a_2310_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0));
v___x_2316_ = l_Lean_Macro_throwError___redArg(v___x_2315_, v_a_2309_, v_a_2310_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
v_a_2318_ = lean_ctor_get(v___x_2316_, 1);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2316_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_inc(v_a_2317_);
lean_dec(v___x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2317_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
else
{
lean_object* v_a_2326_; lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
v_a_2326_ = lean_ctor_get(v___x_2316_, 0);
v_a_2327_ = lean_ctor_get(v___x_2316_, 1);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2316_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_inc(v_a_2326_);
lean_dec(v___x_2316_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2326_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___boxed(lean_object* v_x_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(v_x_2335_, v_a_2336_, v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2338_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrefinePat(void){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = lean_box(0);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2375_ = l_Lean_binderIdent;
v___x_2376_ = lean_unsigned_to_nat(1022u);
v___x_2377_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
v___x_2378_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
lean_ctor_set(v___x_2378_, 1, v___x_2376_);
lean_ctor_set(v___x_2378_, 2, v___x_2375_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat__(void){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2);
return v___x_2379_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2459_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4);
v___x_2460_ = lean_unsigned_to_nat(1022u);
v___x_2461_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2462_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2461_);
lean_ctor_set(v___x_2462_, 1, v___x_2460_);
lean_ctor_set(v___x_2462_, 2, v___x_2459_);
return v___x_2462_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1__(void){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2);
return v___x_2463_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = l_Lean_binderIdent;
v___x_2474_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3));
v___x_2475_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_2476_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2475_);
lean_ctor_set(v___x_2476_, 1, v___x_2474_);
lean_ctor_set(v___x_2476_, 2, v___x_2473_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4);
v___x_2478_ = lean_unsigned_to_nat(1022u);
v___x_2479_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
v___x_2480_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
lean_ctor_set(v___x_2480_, 2, v___x_2477_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f__(void){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(lean_object* v_x_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1));
lean_inc(v_x_2497_);
v___x_2501_ = l_Lean_Syntax_isOfKind(v_x_2497_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_x_2497_);
v___x_2502_ = lean_box(1);
v___x_2503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2502_);
lean_ctor_set(v___x_2503_, 1, v_a_2499_);
return v___x_2503_;
}
else
{
lean_object* v_ref_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_ref_2504_ = lean_ctor_get(v_a_2498_, 5);
v___x_2505_ = lean_unsigned_to_nat(1u);
v___x_2506_ = l_Lean_Syntax_getArg(v_x_2497_, v___x_2505_);
lean_dec(v_x_2497_);
v___x_2507_ = 0;
v___x_2508_ = l_Lean_SourceInfo_fromRef(v_ref_2504_, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
v___x_2510_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2));
lean_inc_n(v___x_2508_, 2);
v___x_2511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2508_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5));
v___x_2513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2508_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_Syntax_node3(v___x_2508_, v___x_2509_, v___x_2511_, v___x_2506_, v___x_2513_);
v___x_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v_a_2499_);
return v___x_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1___boxed(lean_object* v_x_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(v_x_2516_, v_a_2517_, v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2519_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4);
v___x_2527_ = lean_unsigned_to_nat(1022u);
v___x_2528_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
v___x_2529_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
lean_ctor_set(v___x_2529_, 1, v___x_2527_);
lean_ctor_set(v___x_2529_, 2, v___x_2526_);
return v___x_2529_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23__(void){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(lean_object* v_x_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
lean_inc(v_x_2531_);
v___x_2535_ = l_Lean_Syntax_isOfKind(v_x_2531_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v_x_2531_);
v___x_2536_ = lean_box(1);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v_a_2533_);
return v___x_2537_;
}
else
{
lean_object* v_ref_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v_ref_2538_ = lean_ctor_get(v_a_2532_, 5);
v___x_2539_ = lean_unsigned_to_nat(1u);
v___x_2540_ = l_Lean_Syntax_getArg(v_x_2531_, v___x_2539_);
lean_dec(v_x_2531_);
v___x_2541_ = 0;
v___x_2542_ = l_Lean_SourceInfo_fromRef(v_ref_2538_, v___x_2541_);
v___x_2543_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2544_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2));
lean_inc(v___x_2542_);
v___x_2545_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2542_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = l_Lean_Syntax_node2(v___x_2542_, v___x_2543_, v___x_2545_, v___x_2540_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v_a_2533_);
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1___boxed(lean_object* v_x_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(v_x_2548_, v_a_2549_, v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___impl(lean_object* v_x_2552_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_obj_tag_nat(v_x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___impl___boxed(lean_object* v_x_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Parser_Tactic_MRefinePat_ctorIdx___impl(v_x_2554_);
lean_dec_ref(v_x_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(lean_object* v_t_2556_, lean_object* v_k_2557_){
_start:
{
lean_object* v_name_2558_; lean_object* v___x_2559_; 
v_name_2558_ = lean_ctor_get(v_t_2556_, 0);
lean_inc(v_name_2558_);
lean_dec_ref(v_t_2556_);
v___x_2559_ = lean_apply_1(v_k_2557_, v_name_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim(lean_object* v_motive__1_2560_, lean_object* v_ctorIdx_2561_, lean_object* v_t_2562_, lean_object* v_h_2563_, lean_object* v_k_2564_){
_start:
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2562_, v_k_2564_);
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___boxed(lean_object* v_motive__1_2566_, lean_object* v_ctorIdx_2567_, lean_object* v_t_2568_, lean_object* v_h_2569_, lean_object* v_k_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim(v_motive__1_2566_, v_ctorIdx_2567_, v_t_2568_, v_h_2569_, v_k_2570_);
lean_dec(v_ctorIdx_2567_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim___redArg(lean_object* v_t_2572_, lean_object* v_one_2573_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2572_, v_one_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim(lean_object* v_motive__1_2575_, lean_object* v_t_2576_, lean_object* v_h_2577_, lean_object* v_one_2578_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2576_, v_one_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim___redArg(lean_object* v_t_2580_, lean_object* v_tuple_2581_){
_start:
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2580_, v_tuple_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim(lean_object* v_motive__1_2583_, lean_object* v_t_2584_, lean_object* v_h_2585_, lean_object* v_tuple_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2584_, v_tuple_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim___redArg(lean_object* v_t_2588_, lean_object* v_pure_2589_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2588_, v_pure_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim(lean_object* v_motive__1_2591_, lean_object* v_t_2592_, lean_object* v_h_2593_, lean_object* v_pure_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2592_, v_pure_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim___redArg(lean_object* v_t_2596_, lean_object* v_stateful_2597_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2596_, v_stateful_2597_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim(lean_object* v_motive__1_2599_, lean_object* v_t_2600_, lean_object* v_h_2601_, lean_object* v_stateful_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2600_, v_stateful_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim___redArg(lean_object* v_t_2604_, lean_object* v_hole_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2604_, v_hole_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim(lean_object* v_motive__1_2607_, lean_object* v_t_2608_, lean_object* v_h_2609_, lean_object* v_hole_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2608_, v_hole_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2624_, lean_object* v_x_2625_, lean_object* v_x_2626_){
_start:
{
if (lean_obj_tag(v_x_2626_) == 0)
{
lean_dec(v_x_2624_);
return v_x_2625_;
}
else
{
lean_object* v_head_2627_; lean_object* v_tail_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2639_; 
v_head_2627_ = lean_ctor_get(v_x_2626_, 0);
v_tail_2628_ = lean_ctor_get(v_x_2626_, 1);
v_isSharedCheck_2639_ = !lean_is_exclusive(v_x_2626_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2630_ = v_x_2626_;
v_isShared_2631_ = v_isSharedCheck_2639_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_tail_2628_);
lean_inc(v_head_2627_);
lean_dec(v_x_2626_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2639_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
lean_inc(v_x_2624_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set_tag(v___x_2630_, 5);
lean_ctor_set(v___x_2630_, 1, v_x_2624_);
lean_ctor_set(v___x_2630_, 0, v_x_2625_);
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_x_2625_);
lean_ctor_set(v_reuseFailAlloc_2638_, 1, v_x_2624_);
v___x_2633_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_unsigned_to_nat(0u);
v___x_2635_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2627_, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2636_, 0, v___x_2633_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v_x_2625_ = v___x_2636_;
v_x_2626_ = v_tail_2628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(lean_object* v_x_2640_, lean_object* v_x_2641_, lean_object* v_x_2642_){
_start:
{
if (lean_obj_tag(v_x_2642_) == 0)
{
lean_dec(v_x_2640_);
return v_x_2641_;
}
else
{
lean_object* v_head_2643_; lean_object* v_tail_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2655_; 
v_head_2643_ = lean_ctor_get(v_x_2642_, 0);
v_tail_2644_ = lean_ctor_get(v_x_2642_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_x_2642_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2646_ = v_x_2642_;
v_isShared_2647_ = v_isSharedCheck_2655_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_tail_2644_);
lean_inc(v_head_2643_);
lean_dec(v_x_2642_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2655_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
lean_inc(v_x_2640_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set_tag(v___x_2646_, 5);
lean_ctor_set(v___x_2646_, 1, v_x_2640_);
lean_ctor_set(v___x_2646_, 0, v_x_2641_);
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_x_2641_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_x_2640_);
v___x_2649_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2650_ = lean_unsigned_to_nat(0u);
v___x_2651_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2643_, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2649_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(v_x_2640_, v___x_2652_, v_tail_2644_);
return v___x_2653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(lean_object* v_x_2656_, lean_object* v_x_2657_){
_start:
{
if (lean_obj_tag(v_x_2656_) == 0)
{
lean_object* v___x_2658_; 
lean_dec(v_x_2657_);
v___x_2658_ = lean_box(0);
return v___x_2658_;
}
else
{
lean_object* v_tail_2659_; 
v_tail_2659_ = lean_ctor_get(v_x_2656_, 1);
if (lean_obj_tag(v_tail_2659_) == 0)
{
lean_object* v_head_2660_; lean_object* v___x_2661_; 
lean_dec(v_x_2657_);
v_head_2660_ = lean_ctor_get(v_x_2656_, 0);
lean_inc(v_head_2660_);
lean_dec_ref_known(v_x_2656_, 2);
v___x_2661_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2660_);
return v___x_2661_;
}
else
{
lean_object* v_head_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_inc(v_tail_2659_);
v_head_2662_ = lean_ctor_get(v_x_2656_, 0);
lean_inc(v_head_2662_);
lean_dec_ref_known(v_x_2656_, 2);
v___x_2663_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2662_);
v___x_2664_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(v_x_2657_, v___x_2663_, v_tail_2659_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(lean_object* v_a_2665_){
_start:
{
if (lean_obj_tag(v_a_2665_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1));
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2667_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3));
v___x_2668_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(v_a_2665_, v___x_2667_);
v___x_2669_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5);
v___x_2670_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6));
v___x_2671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v___x_2668_);
v___x_2672_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7));
v___x_2673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2671_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2669_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = 0;
v___x_2676_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set_uint8(v___x_2676_, sizeof(void*)*1, v___x_2675_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr(lean_object* v_x_2695_, lean_object* v_prec_2696_){
_start:
{
switch(lean_obj_tag(v_x_2695_))
{
case 0:
{
lean_object* v_name_2697_; lean_object* v___y_2699_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v_name_2697_ = lean_ctor_get(v_x_2695_, 0);
lean_inc(v_name_2697_);
lean_dec_ref_known(v_x_2695_, 1);
v___x_2707_ = lean_unsigned_to_nat(1024u);
v___x_2708_ = lean_nat_dec_le(v___x_2707_, v_prec_2696_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; 
v___x_2709_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2699_ = v___x_2709_;
goto v___jp_2698_;
}
else
{
lean_object* v___x_2710_; 
v___x_2710_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2699_ = v___x_2710_;
goto v___jp_2698_;
}
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2700_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2));
v___x_2701_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2697_);
v___x_2702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_inc(v___y_2699_);
v___x_2703_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2699_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = 0;
v___x_2705_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set_uint8(v___x_2705_, sizeof(void*)*1, v___x_2704_);
v___x_2706_ = l_Repr_addAppParen(v___x_2705_, v_prec_2696_);
return v___x_2706_;
}
}
case 1:
{
lean_object* v_args_2711_; lean_object* v___y_2713_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_args_2711_ = lean_ctor_get(v_x_2695_, 0);
lean_inc(v_args_2711_);
lean_dec_ref_known(v_x_2695_, 1);
v___x_2721_ = lean_unsigned_to_nat(1024u);
v___x_2722_ = lean_nat_dec_le(v___x_2721_, v_prec_2696_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2713_ = v___x_2723_;
goto v___jp_2712_;
}
else
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2713_ = v___x_2724_;
goto v___jp_2712_;
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2714_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5));
v___x_2715_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_args_2711_);
v___x_2716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
lean_inc(v___y_2713_);
v___x_2717_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___y_2713_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = 0;
v___x_2719_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set_uint8(v___x_2719_, sizeof(void*)*1, v___x_2718_);
v___x_2720_ = l_Repr_addAppParen(v___x_2719_, v_prec_2696_);
return v___x_2720_;
}
}
case 2:
{
lean_object* v_h_2725_; lean_object* v___y_2727_; lean_object* v___x_2735_; uint8_t v___x_2736_; 
v_h_2725_ = lean_ctor_get(v_x_2695_, 0);
lean_inc(v_h_2725_);
lean_dec_ref_known(v_x_2695_, 1);
v___x_2735_ = lean_unsigned_to_nat(1024u);
v___x_2736_ = lean_nat_dec_le(v___x_2735_, v_prec_2696_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2727_ = v___x_2737_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2727_ = v___x_2738_;
goto v___jp_2726_;
}
v___jp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2728_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8));
v___x_2729_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2725_);
v___x_2730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
lean_inc(v___y_2727_);
v___x_2731_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___y_2727_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = 0;
v___x_2733_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set_uint8(v___x_2733_, sizeof(void*)*1, v___x_2732_);
v___x_2734_ = l_Repr_addAppParen(v___x_2733_, v_prec_2696_);
return v___x_2734_;
}
}
case 3:
{
lean_object* v_h_2739_; lean_object* v___y_2741_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_h_2739_ = lean_ctor_get(v_x_2695_, 0);
lean_inc(v_h_2739_);
lean_dec_ref_known(v_x_2695_, 1);
v___x_2749_ = lean_unsigned_to_nat(1024u);
v___x_2750_ = lean_nat_dec_le(v___x_2749_, v_prec_2696_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2741_ = v___x_2751_;
goto v___jp_2740_;
}
else
{
lean_object* v___x_2752_; 
v___x_2752_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2741_ = v___x_2752_;
goto v___jp_2740_;
}
v___jp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2742_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11));
v___x_2743_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2739_);
v___x_2744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
lean_inc(v___y_2741_);
v___x_2745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___y_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = 0;
v___x_2747_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2747_, 0, v___x_2745_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*1, v___x_2746_);
v___x_2748_ = l_Repr_addAppParen(v___x_2747_, v_prec_2696_);
return v___x_2748_;
}
}
default: 
{
lean_object* v_name_2753_; lean_object* v___y_2755_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v_name_2753_ = lean_ctor_get(v_x_2695_, 0);
lean_inc(v_name_2753_);
lean_dec_ref_known(v_x_2695_, 1);
v___x_2763_ = lean_unsigned_to_nat(1024u);
v___x_2764_ = lean_nat_dec_le(v___x_2763_, v_prec_2696_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2755_ = v___x_2765_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2755_ = v___x_2766_;
goto v___jp_2754_;
}
v___jp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2756_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14));
v___x_2757_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2753_);
v___x_2758_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
lean_inc(v___y_2755_);
v___x_2759_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___y_2755_);
lean_ctor_set(v___x_2759_, 1, v___x_2758_);
v___x_2760_ = 0;
v___x_2761_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2761_, 0, v___x_2759_);
lean_ctor_set_uint8(v___x_2761_, sizeof(void*)*1, v___x_2760_);
v___x_2762_ = l_Repr_addAppParen(v___x_2761_, v_prec_2696_);
return v___x_2762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(lean_object* v___y_2767_){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v___y_2767_, v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___boxed(lean_object* v_x_2770_, lean_object* v_prec_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_x_2770_, v_prec_2771_);
lean_dec(v_prec_2771_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(lean_object* v_a_2773_, lean_object* v_n_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_a_2773_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___boxed(lean_object* v_a_2776_, lean_object* v_n_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(v_a_2776_, v_n_2777_);
lean_dec(v_n_2777_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(size_t v_sz_2785_, size_t v_i_2786_, lean_object* v_bs_2787_){
_start:
{
uint8_t v___x_2788_; 
v___x_2788_ = lean_usize_dec_lt(v_i_2786_, v_sz_2785_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
v___x_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_bs_2787_);
return v___x_2789_;
}
else
{
lean_object* v_v_2790_; lean_object* v___x_2791_; lean_object* v_bs_x27_2792_; size_t v___x_2793_; size_t v___x_2794_; lean_object* v___x_2795_; 
v_v_2790_ = lean_array_uget(v_bs_2787_, v_i_2786_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v_bs_x27_2792_ = lean_array_uset(v_bs_2787_, v_i_2786_, v___x_2791_);
v___x_2793_ = ((size_t)1ULL);
v___x_2794_ = lean_usize_add(v_i_2786_, v___x_2793_);
v___x_2795_ = lean_array_uset(v_bs_x27_2792_, v_i_2786_, v_v_2790_);
v_i_2786_ = v___x_2794_;
v_bs_2787_ = v___x_2795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0___boxed(lean_object* v_sz_2797_, lean_object* v_i_2798_, lean_object* v_bs_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2797_);
lean_dec(v_sz_2797_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2798_);
lean_dec(v_i_2798_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_boxed_2800_, v_i_boxed_2801_, v_bs_2799_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse_go(lean_object* v_a_2803_){
_start:
{
lean_object* v___y_2805_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v___x_2830_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
lean_inc(v_a_2803_);
v___x_2831_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
lean_inc(v_a_2803_);
v___x_2833_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2834_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1));
lean_inc(v_a_2803_);
v___x_2835_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; uint8_t v___x_2837_; 
v___x_2836_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
lean_inc(v_a_2803_);
v___x_2837_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; uint8_t v___x_2839_; 
v___x_2838_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
lean_inc(v_a_2803_);
v___x_2839_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1));
lean_inc(v_a_2803_);
v___x_2841_ = l_Lean_Syntax_isOfKind(v_a_2803_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_object* v___x_2842_; 
lean_dec(v_a_2803_);
v___x_2842_ = lean_box(0);
return v___x_2842_;
}
else
{
lean_object* v___x_2843_; lean_object* v_pat_2844_; 
v___x_2843_ = lean_unsigned_to_nat(1u);
v_pat_2844_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2843_);
lean_dec(v_a_2803_);
v_a_2803_ = v_pat_2844_;
goto _start;
}
}
else
{
lean_object* v___x_2846_; lean_object* v_h_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2846_ = lean_unsigned_to_nat(1u);
v_h_2847_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2846_);
lean_dec(v_a_2803_);
v___x_2848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_h_2847_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
return v___x_2849_;
}
}
else
{
lean_object* v___x_2850_; lean_object* v_h_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2850_ = lean_unsigned_to_nat(1u);
v_h_2851_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2850_);
lean_dec(v_a_2803_);
v___x_2852_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2852_, 0, v_h_2851_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2854_ = lean_unsigned_to_nat(1u);
v___x_2855_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2854_);
lean_dec(v_a_2803_);
v___x_2856_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePats___closed__1));
lean_inc(v___x_2855_);
v___x_2857_ = l_Lean_Syntax_isOfKind(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec(v___x_2855_);
v___x_2858_ = lean_box(0);
return v___x_2858_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2859_);
lean_dec(v___x_2855_);
v___x_2861_ = l_Lean_Syntax_getArgs(v___x_2860_);
lean_dec(v___x_2860_);
v___x_2862_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___x_2863_ = lean_array_get_size(v___x_2861_);
v___x_2864_ = lean_nat_dec_lt(v___x_2859_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_dec_ref(v___x_2861_);
v___y_2805_ = v___x_2862_;
goto v___jp_2804_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; lean_object* v___x_2869_; lean_object* v_snd_2870_; 
v___x_2865_ = lean_box(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2862_);
v___x_2867_ = ((size_t)0ULL);
v___x_2868_ = lean_usize_of_nat(v___x_2863_);
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2857_, v___x_2833_, v___x_2861_, v___x_2867_, v___x_2868_, v___x_2866_);
lean_dec_ref(v___x_2861_);
v_snd_2870_ = lean_ctor_get(v___x_2869_, 1);
lean_inc(v_snd_2870_);
lean_dec_ref(v___x_2869_);
v___y_2805_ = v_snd_2870_;
goto v___jp_2804_;
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v_name_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2871_ = lean_unsigned_to_nat(1u);
v_name_2872_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2871_);
lean_dec(v_a_2803_);
v___x_2873_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2873_, 0, v_name_2872_);
v___x_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
}
else
{
lean_object* v___x_2875_; lean_object* v_name_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2875_ = lean_unsigned_to_nat(0u);
v_name_2876_ = l_Lean_Syntax_getArg(v_a_2803_, v___x_2875_);
lean_dec(v_a_2803_);
v___x_2877_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2876_);
v___x_2878_ = l_Lean_Syntax_isOfKind(v_name_2876_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; 
lean_dec(v_name_2876_);
v___x_2879_ = lean_box(0);
return v___x_2879_;
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_name_2876_);
v___x_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2880_);
return v___x_2881_;
}
}
v___jp_2804_:
{
size_t v_sz_2806_; size_t v___x_2807_; lean_object* v___x_2808_; 
v_sz_2806_ = lean_array_size(v___y_2805_);
v___x_2807_ = ((size_t)0ULL);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_2806_, v___x_2807_, v___y_2805_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v___x_2809_; 
v___x_2809_ = lean_box(0);
return v___x_2809_;
}
else
{
lean_object* v_val_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2829_; 
v_val_2810_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2812_ = v___x_2808_;
v_isShared_2813_ = v_isSharedCheck_2829_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_val_2810_);
lean_dec(v___x_2808_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2829_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
size_t v_sz_2814_; lean_object* v___x_2815_; 
v_sz_2814_ = lean_array_size(v_val_2810_);
v___x_2815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_2814_, v___x_2807_, v_val_2810_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2816_; 
lean_del_object(v___x_2812_);
v___x_2816_ = lean_box(0);
return v___x_2816_;
}
else
{
lean_object* v_val_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2828_; 
v_val_2817_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2819_ = v___x_2815_;
v_isShared_2820_ = v_isSharedCheck_2828_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_val_2817_);
lean_dec(v___x_2815_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2828_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2823_; 
v___x_2821_ = lean_array_to_list(v_val_2817_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2821_);
v___x_2823_ = v___x_2812_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2825_; 
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2823_);
v___x_2825_ = v___x_2819_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v___x_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(size_t v_sz_2882_, size_t v_i_2883_, lean_object* v_bs_2884_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_usize_dec_lt(v_i_2883_, v_sz_2882_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_bs_2884_);
return v___x_2886_;
}
else
{
lean_object* v_v_2887_; lean_object* v___x_2888_; 
v_v_2887_ = lean_array_uget_borrowed(v_bs_2884_, v_i_2883_);
lean_inc(v_v_2887_);
v___x_2888_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_v_2887_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2889_; 
lean_dec_ref(v_bs_2884_);
v___x_2889_ = lean_box(0);
return v___x_2889_;
}
else
{
lean_object* v_val_2890_; lean_object* v___x_2891_; lean_object* v_bs_x27_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; 
v_val_2890_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_val_2890_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2891_ = lean_unsigned_to_nat(0u);
v_bs_x27_2892_ = lean_array_uset(v_bs_2884_, v_i_2883_, v___x_2891_);
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_add(v_i_2883_, v___x_2893_);
v___x_2895_ = lean_array_uset(v_bs_x27_2892_, v_i_2883_, v_val_2890_);
v_i_2883_ = v___x_2894_;
v_bs_2884_ = v___x_2895_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1___boxed(lean_object* v_sz_2897_, lean_object* v_i_2898_, lean_object* v_bs_2899_){
_start:
{
size_t v_sz_boxed_2900_; size_t v_i_boxed_2901_; lean_object* v_res_2902_; 
v_sz_boxed_2900_ = lean_unbox_usize(v_sz_2897_);
lean_dec(v_sz_2897_);
v_i_boxed_2901_ = lean_unbox_usize(v_i_2898_);
lean_dec(v_i_2898_);
v_res_2902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_boxed_2900_, v_i_boxed_2901_, v_bs_2899_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse(lean_object* v_pat_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___f_2906_; lean_object* v___x_2907_; 
v___f_2906_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2904_);
v___x_2907_ = l_Lean_expandMacros(v_pat_2903_, v___f_2906_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2919_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v_a_2909_ = lean_ctor_get(v___x_2907_, 1);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2911_ = v___x_2907_;
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_inc(v_a_2908_);
lean_dec(v___x_2907_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2919_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_a_2908_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; 
lean_del_object(v___x_2911_);
v___x_2914_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2909_);
return v___x_2914_;
}
else
{
lean_object* v_val_2915_; lean_object* v___x_2917_; 
v_val_2915_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v___x_2913_, 1);
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v_val_2915_);
v___x_2917_ = v___x_2911_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_val_2915_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_a_2909_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
v_a_2920_ = lean_ctor_get(v___x_2907_, 0);
v_a_2921_ = lean_ctor_get(v___x_2907_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2907_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_inc(v_a_2920_);
lean_dec(v___x_2907_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2920_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse___boxed(lean_object* v_pat_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Parser_Tactic_MRefinePat_parse(v_pat_2929_, v_a_2930_, v_a_2931_);
lean_dec_ref(v_a_2930_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(lean_object* v_x_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefineError___closed__1));
v___x_2967_ = l_Lean_Syntax_isOfKind(v_x_2963_, v___x_2966_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_box(1);
v___x_2969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v_a_2965_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0));
v___x_2971_ = l_Lean_Macro_throwError___redArg(v___x_2970_, v_a_2964_, v_a_2965_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
v_a_2973_ = lean_ctor_get(v___x_2971_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2971_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_inc(v_a_2972_);
lean_dec(v___x_2971_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2972_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
v_a_2981_ = lean_ctor_get(v___x_2971_, 0);
v_a_2982_ = lean_ctor_get(v___x_2971_, 1);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2971_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_inc(v_a_2981_);
lean_dec(v___x_2971_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2981_);
lean_ctor_set(v_reuseFailAlloc_2988_, 1, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___boxed(lean_object* v_x_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(v_x_2990_, v_a_2991_, v_a_2992_);
lean_dec_ref(v_a_2991_);
return v_res_2993_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mintroPat(void){
_start:
{
lean_object* v___x_3023_; 
v___x_3023_ = lean_box(0);
return v___x_3023_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = l_Lean_binderIdent;
v___x_3045_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3));
v___x_3046_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3047_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v___x_3045_);
lean_ctor_set(v___x_3047_, 2, v___x_3044_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3048_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4);
v___x_3049_ = lean_unsigned_to_nat(1022u);
v___x_3050_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1));
v___x_3051_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
lean_ctor_set(v___x_3051_, 1, v___x_3049_);
lean_ctor_set(v___x_3051_, 2, v___x_3048_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200__(void){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(lean_object* v_x_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroError___closed__1));
v___x_3094_ = l_Lean_Syntax_isOfKind(v_x_3090_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
v___x_3095_ = lean_box(1);
v___x_3096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
lean_ctor_set(v___x_3096_, 1, v_a_3092_);
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0));
v___x_3098_ = l_Lean_Macro_throwError___redArg(v___x_3097_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
v_a_3100_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3098_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_inc(v_a_3099_);
lean_dec(v___x_3098_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3099_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3108_ = lean_ctor_get(v___x_3098_, 0);
v_a_3109_ = lean_ctor_get(v___x_3098_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3098_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_inc(v_a_3108_);
lean_dec(v___x_3098_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3108_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___boxed(lean_object* v_x_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(v_x_3117_, v_a_3118_, v_a_3119_);
lean_dec_ref(v_a_3118_);
return v_res_3120_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3(void){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2));
v___x_3129_ = l_String_toRawSubstring_x27(v___x_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3137_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__0));
v___x_3138_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__1));
lean_inc(v_x_3134_);
v___x_3139_ = l_Lean_Syntax_isOfKind(v_x_3134_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec(v_x_3134_);
v___x_3140_ = lean_box(1);
v___x_3141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
lean_ctor_set(v___x_3141_, 1, v_a_3136_);
return v___x_3141_;
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3142_ = lean_unsigned_to_nat(0u);
v___x_3143_ = lean_unsigned_to_nat(1u);
v___x_3144_ = l_Lean_Syntax_getArg(v_x_3134_, v___x_3143_);
lean_dec(v_x_3134_);
v___x_3145_ = lean_unsigned_to_nat(2u);
v___x_3146_ = l_Lean_Syntax_getNumArgs(v___x_3144_);
v___x_3147_ = lean_nat_dec_le(v___x_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
uint8_t v___x_3148_; 
lean_dec(v___x_3146_);
lean_inc(v___x_3144_);
v___x_3148_ = l_Lean_Syntax_matchesNull(v___x_3144_, v___x_3143_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v___x_3144_);
v___x_3149_ = lean_box(1);
v___x_3150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
lean_ctor_set(v___x_3150_, 1, v_a_3136_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3151_ = l_Lean_Syntax_getArg(v___x_3144_, v___x_3142_);
lean_dec(v___x_3144_);
v___x_3152_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat___00__closed__1));
lean_inc(v___x_3151_);
v___x_3153_ = l_Lean_Syntax_isOfKind(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec(v___x_3151_);
v___x_3154_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3136_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; uint8_t v___x_3157_; 
v___x_3155_ = l_Lean_Syntax_getArg(v___x_3151_, v___x_3142_);
lean_dec(v___x_3151_);
v___x_3156_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
lean_inc(v___x_3155_);
v___x_3157_ = l_Lean_Syntax_isOfKind(v___x_3155_, v___x_3156_);
if (v___x_3157_ == 0)
{
lean_object* v_quotContext_3158_; lean_object* v_currMacroScope_3159_; lean_object* v_ref_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; 
v_quotContext_3158_ = lean_ctor_get(v_a_3135_, 1);
v_currMacroScope_3159_ = lean_ctor_get(v_a_3135_, 2);
v_ref_3160_ = lean_ctor_get(v_a_3135_, 5);
v___x_3161_ = l_Lean_SourceInfo_fromRef(v_ref_3160_, v___x_3157_);
v___x_3162_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3163_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3161_, 12);
v___x_3164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3161_);
lean_ctor_set(v___x_3164_, 1, v___x_3137_);
v___x_3165_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3166_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3167_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3159_);
lean_inc(v_quotContext_3158_);
v___x_3168_ = l_Lean_addMacroScope(v_quotContext_3158_, v___x_3167_, v_currMacroScope_3159_);
v___x_3169_ = lean_box(0);
v___x_3170_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3170_, 0, v___x_3161_);
lean_ctor_set(v___x_3170_, 1, v___x_3166_);
lean_ctor_set(v___x_3170_, 2, v___x_3168_);
lean_ctor_set(v___x_3170_, 3, v___x_3169_);
lean_inc_ref(v___x_3170_);
v___x_3171_ = l_Lean_Syntax_node1(v___x_3161_, v___x_3165_, v___x_3170_);
v___x_3172_ = l_Lean_Syntax_node1(v___x_3161_, v___x_3156_, v___x_3171_);
v___x_3173_ = l_Lean_Syntax_node1(v___x_3161_, v___x_3152_, v___x_3172_);
v___x_3174_ = l_Lean_Syntax_node1(v___x_3161_, v___x_3163_, v___x_3173_);
v___x_3175_ = l_Lean_Syntax_node2(v___x_3161_, v___x_3138_, v___x_3164_, v___x_3174_);
v___x_3176_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3161_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3179_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3161_);
lean_ctor_set(v___x_3180_, 1, v___x_3178_);
v___x_3181_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3161_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_Syntax_node4(v___x_3161_, v___x_3179_, v___x_3180_, v___x_3170_, v___x_3182_, v___x_3155_);
v___x_3184_ = l_Lean_Syntax_node3(v___x_3161_, v___x_3163_, v___x_3175_, v___x_3177_, v___x_3183_);
v___x_3185_ = l_Lean_Syntax_node1(v___x_3161_, v___x_3162_, v___x_3184_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3185_);
lean_ctor_set(v___x_3186_, 1, v_a_3136_);
return v___x_3186_;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3187_ = l_Lean_Syntax_getArg(v___x_3155_, v___x_3142_);
v___x_3188_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3189_ = l_Lean_Syntax_isOfKind(v___x_3187_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_object* v_quotContext_3190_; lean_object* v_currMacroScope_3191_; lean_object* v_ref_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_quotContext_3190_ = lean_ctor_get(v_a_3135_, 1);
v_currMacroScope_3191_ = lean_ctor_get(v_a_3135_, 2);
v_ref_3192_ = lean_ctor_get(v_a_3135_, 5);
v___x_3193_ = l_Lean_SourceInfo_fromRef(v_ref_3192_, v___x_3189_);
v___x_3194_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3195_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3193_, 12);
v___x_3196_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3193_);
lean_ctor_set(v___x_3196_, 1, v___x_3137_);
v___x_3197_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3198_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3191_);
lean_inc(v_quotContext_3190_);
v___x_3199_ = l_Lean_addMacroScope(v_quotContext_3190_, v___x_3198_, v_currMacroScope_3191_);
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3193_);
lean_ctor_set(v___x_3201_, 1, v___x_3197_);
lean_ctor_set(v___x_3201_, 2, v___x_3199_);
lean_ctor_set(v___x_3201_, 3, v___x_3200_);
lean_inc_ref(v___x_3201_);
v___x_3202_ = l_Lean_Syntax_node1(v___x_3193_, v___x_3188_, v___x_3201_);
v___x_3203_ = l_Lean_Syntax_node1(v___x_3193_, v___x_3156_, v___x_3202_);
v___x_3204_ = l_Lean_Syntax_node1(v___x_3193_, v___x_3152_, v___x_3203_);
v___x_3205_ = l_Lean_Syntax_node1(v___x_3193_, v___x_3195_, v___x_3204_);
v___x_3206_ = l_Lean_Syntax_node2(v___x_3193_, v___x_3138_, v___x_3196_, v___x_3205_);
v___x_3207_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3193_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v___x_3209_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3210_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3193_);
lean_ctor_set(v___x_3211_, 1, v___x_3209_);
v___x_3212_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3193_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_Syntax_node4(v___x_3193_, v___x_3210_, v___x_3211_, v___x_3201_, v___x_3213_, v___x_3155_);
v___x_3215_ = l_Lean_Syntax_node3(v___x_3193_, v___x_3195_, v___x_3206_, v___x_3208_, v___x_3214_);
v___x_3216_ = l_Lean_Syntax_node1(v___x_3193_, v___x_3194_, v___x_3215_);
v___x_3217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
lean_ctor_set(v___x_3217_, 1, v_a_3136_);
return v___x_3217_;
}
else
{
lean_object* v___x_3218_; 
lean_dec(v___x_3155_);
v___x_3218_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3136_);
return v___x_3218_;
}
}
}
}
}
else
{
lean_object* v_ref_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_pats_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; 
v_ref_3219_ = lean_ctor_get(v_a_3135_, 5);
v___x_3220_ = l_Lean_Syntax_getArg(v___x_3144_, v___x_3142_);
v___x_3221_ = l_Lean_Syntax_getArg(v___x_3144_, v___x_3143_);
v___x_3222_ = l_Lean_Syntax_getArgs(v___x_3144_);
lean_dec(v___x_3144_);
v___x_3223_ = l_Array_extract___redArg(v___x_3222_, v___x_3145_, v___x_3146_);
lean_dec_ref(v___x_3222_);
v___x_3224_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3225_ = lean_box(2);
v___x_3226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
lean_ctor_set(v___x_3226_, 1, v___x_3224_);
lean_ctor_set(v___x_3226_, 2, v___x_3223_);
v_pats_3227_ = l_Lean_Syntax_getArgs(v___x_3226_);
lean_dec_ref_known(v___x_3226_, 3);
v___x_3228_ = 0;
v___x_3229_ = l_Lean_SourceInfo_fromRef(v_ref_3219_, v___x_3228_);
v___x_3230_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3229_, 7);
v___x_3231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3229_);
lean_ctor_set(v___x_3231_, 1, v___x_3137_);
v___x_3232_ = l_Lean_Syntax_node1(v___x_3229_, v___x_3224_, v___x_3220_);
lean_inc_ref(v___x_3231_);
v___x_3233_ = l_Lean_Syntax_node2(v___x_3229_, v___x_3138_, v___x_3231_, v___x_3232_);
v___x_3234_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3229_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Array_mkArray1___redArg(v___x_3221_);
v___x_3237_ = l_Array_append___redArg(v___x_3236_, v_pats_3227_);
lean_dec_ref(v_pats_3227_);
v___x_3238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3229_);
lean_ctor_set(v___x_3238_, 1, v___x_3224_);
lean_ctor_set(v___x_3238_, 2, v___x_3237_);
v___x_3239_ = l_Lean_Syntax_node2(v___x_3229_, v___x_3138_, v___x_3231_, v___x_3238_);
v___x_3240_ = l_Lean_Syntax_node3(v___x_3229_, v___x_3224_, v___x_3233_, v___x_3235_, v___x_3239_);
v___x_3241_ = l_Lean_Syntax_node1(v___x_3229_, v___x_3230_, v___x_3240_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3241_);
lean_ctor_set(v___x_3242_, 1, v_a_3136_);
return v___x_3242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object* v_x_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(v_x_3243_, v_a_3244_, v_a_3245_);
lean_dec_ref(v_a_3244_);
return v_res_3246_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrevertPat(void){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_box(0);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(lean_object* v_x_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevertError___closed__1));
v___x_3352_ = l_Lean_Syntax_isOfKind(v_x_3348_, v___x_3351_);
if (v___x_3352_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_box(1);
v___x_3354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set(v___x_3354_, 1, v_a_3350_);
return v___x_3354_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0));
v___x_3356_ = l_Lean_Macro_throwError___redArg(v___x_3355_, v_a_3349_, v_a_3350_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_a_3358_ = lean_ctor_get(v___x_3356_, 1);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3356_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3357_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
else
{
lean_object* v_a_3366_; lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3366_ = lean_ctor_get(v___x_3356_, 0);
v_a_3367_ = lean_ctor_get(v___x_3356_, 1);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3356_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_inc(v_a_3366_);
lean_dec(v___x_3356_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3366_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___boxed(lean_object* v_x_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_){
_start:
{
lean_object* v_res_3378_; 
v_res_3378_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(v_x_3375_, v_a_3376_, v_a_3377_);
lean_dec_ref(v_a_3376_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(lean_object* v_x_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3382_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__0));
v___x_3383_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__1));
lean_inc(v_x_3379_);
v___x_3384_ = l_Lean_Syntax_isOfKind(v_x_3379_, v___x_3383_);
if (v___x_3384_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec(v_x_3379_);
v___x_3385_ = lean_box(1);
v___x_3386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v_a_3381_);
return v___x_3386_;
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v___x_3387_ = lean_unsigned_to_nat(1u);
v___x_3388_ = l_Lean_Syntax_getArg(v_x_3379_, v___x_3387_);
lean_dec(v_x_3379_);
v___x_3389_ = lean_unsigned_to_nat(2u);
v___x_3390_ = l_Lean_Syntax_getNumArgs(v___x_3388_);
v___x_3391_ = lean_nat_dec_le(v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
lean_dec(v___x_3390_);
lean_dec(v___x_3388_);
v___x_3392_ = lean_box(1);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v_a_3381_);
return v___x_3393_;
}
else
{
lean_object* v_ref_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v_pats_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_ref_3394_ = lean_ctor_get(v_a_3380_, 5);
v___x_3395_ = lean_unsigned_to_nat(0u);
v___x_3396_ = l_Lean_Syntax_getArg(v___x_3388_, v___x_3395_);
v___x_3397_ = l_Lean_Syntax_getArg(v___x_3388_, v___x_3387_);
v___x_3398_ = l_Lean_Syntax_getArgs(v___x_3388_);
lean_dec(v___x_3388_);
v___x_3399_ = l_Array_extract___redArg(v___x_3398_, v___x_3389_, v___x_3390_);
lean_dec_ref(v___x_3398_);
v___x_3400_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3401_ = lean_box(2);
v___x_3402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3400_);
lean_ctor_set(v___x_3402_, 2, v___x_3399_);
v_pats_3403_ = l_Lean_Syntax_getArgs(v___x_3402_);
lean_dec_ref_known(v___x_3402_, 3);
v___x_3404_ = 0;
v___x_3405_ = l_Lean_SourceInfo_fromRef(v_ref_3394_, v___x_3404_);
v___x_3406_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3405_, 7);
v___x_3407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3382_);
v___x_3408_ = l_Lean_Syntax_node1(v___x_3405_, v___x_3400_, v___x_3396_);
lean_inc_ref(v___x_3407_);
v___x_3409_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3383_, v___x_3407_, v___x_3408_);
v___x_3410_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3405_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Array_mkArray1___redArg(v___x_3397_);
v___x_3413_ = l_Array_append___redArg(v___x_3412_, v_pats_3403_);
lean_dec_ref(v_pats_3403_);
v___x_3414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3405_);
lean_ctor_set(v___x_3414_, 1, v___x_3400_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
v___x_3415_ = l_Lean_Syntax_node2(v___x_3405_, v___x_3383_, v___x_3407_, v___x_3414_);
v___x_3416_ = l_Lean_Syntax_node3(v___x_3405_, v___x_3400_, v___x_3409_, v___x_3411_, v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node1(v___x_3405_, v___x_3406_, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v_a_3381_);
return v___x_3418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1___boxed(lean_object* v_x_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(v_x_3419_, v_a_3420_, v_a_3421_);
lean_dec_ref(v_a_3420_);
return v_res_3422_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8(void){
_start:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; 
v___x_3488_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7));
v___x_3489_ = l_Lean_mkIdent(v___x_3488_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(lean_object* v_x_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3519_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v___x_3562_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
lean_inc(v_x_3491_);
v___x_3563_ = l_Lean_Syntax_isOfKind(v_x_3491_, v___x_3562_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec(v_x_3491_);
v___x_3564_ = lean_box(1);
v___x_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
lean_ctor_set(v___x_3565_, 1, v_a_3493_);
return v___x_3565_;
}
else
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_unsigned_to_nat(1u);
v___x_3567_ = l_Lean_Syntax_getArg(v_x_3491_, v___x_3566_);
lean_dec(v_x_3491_);
v___x_3568_ = l_Lean_Syntax_getOptional_x3f(v___x_3567_);
lean_dec(v___x_3567_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v___x_3569_; 
v___x_3569_ = lean_box(0);
v___y_3519_ = v___x_3569_;
goto v___jp_3518_;
}
else
{
lean_object* v_val_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_val_3570_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3568_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_val_3570_);
lean_dec(v___x_3568_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_val_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
v___y_3519_ = v___x_3575_;
goto v___jp_3518_;
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
lean_inc_ref(v___y_3502_);
v___x_3509_ = l_Array_append___redArg(v___y_3502_, v___y_3508_);
lean_dec_ref(v___y_3508_);
lean_inc(v___y_3496_);
lean_inc_n(v___y_3498_, 6);
v___x_3510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3510_, 0, v___y_3498_);
lean_ctor_set(v___x_3510_, 1, v___y_3496_);
lean_ctor_set(v___x_3510_, 2, v___x_3509_);
v___x_3511_ = l_Lean_Syntax_node2(v___y_3498_, v___y_3499_, v___y_3495_, v___x_3510_);
lean_inc(v___y_3501_);
v___x_3512_ = l_Lean_Syntax_node3(v___y_3498_, v___y_3501_, v___y_3504_, v___y_3497_, v___x_3511_);
v___x_3513_ = l_Lean_Syntax_node1(v___y_3498_, v___y_3496_, v___x_3512_);
v___x_3514_ = l_Lean_Syntax_node1(v___y_3498_, v___y_3505_, v___x_3513_);
v___x_3515_ = l_Lean_Syntax_node1(v___y_3498_, v___y_3507_, v___x_3514_);
v___x_3516_ = l_Lean_Syntax_node3(v___y_3498_, v___y_3500_, v___y_3506_, v___x_3515_, v___y_3503_);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_a_3493_);
return v___x_3517_;
}
v___jp_3518_:
{
lean_object* v_ref_3520_; uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_ref_3520_ = lean_ctor_get(v_a_3492_, 5);
v___x_3521_ = 0;
v___x_3522_ = l_Lean_SourceInfo_fromRef(v_ref_3520_, v___x_3521_);
v___x_3523_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3524_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3522_, 20);
v___x_3525_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3522_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3527_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3528_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3529_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1));
v___x_3530_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3531_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3532_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3522_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3));
v___x_3534_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4));
v___x_3535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3522_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__1));
v___x_3537_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__2));
v___x_3538_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3522_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8);
v___x_3540_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3528_, v___x_3539_);
lean_inc_ref(v___x_3538_);
v___x_3541_ = l_Lean_Syntax_node2(v___x_3522_, v___x_3536_, v___x_3538_, v___x_3540_);
v___x_3542_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3528_, v___x_3541_);
v___x_3543_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3527_, v___x_3542_);
v___x_3544_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3526_, v___x_3543_);
v___x_3545_ = l_Lean_Syntax_node2(v___x_3522_, v___x_3533_, v___x_3535_, v___x_3544_);
v___x_3546_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3528_, v___x_3545_);
v___x_3547_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3527_, v___x_3546_);
v___x_3548_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3526_, v___x_3547_);
v___x_3549_ = l_Lean_Syntax_node2(v___x_3522_, v___x_3530_, v___x_3532_, v___x_3548_);
v___x_3550_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3528_, v___x_3549_);
v___x_3551_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3527_, v___x_3550_);
v___x_3552_ = l_Lean_Syntax_node1(v___x_3522_, v___x_3526_, v___x_3551_);
v___x_3553_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3522_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
lean_inc_ref(v___x_3554_);
lean_inc_ref(v___x_3525_);
v___x_3555_ = l_Lean_Syntax_node3(v___x_3522_, v___x_3523_, v___x_3525_, v___x_3552_, v___x_3554_);
v___x_3556_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9));
v___x_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3522_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3519_) == 1)
{
lean_object* v_val_3559_; lean_object* v___x_3560_; 
v_val_3559_ = lean_ctor_get(v___y_3519_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v___y_3519_, 1);
v___x_3560_ = l_Array_mkArray1___redArg(v_val_3559_);
v___y_3495_ = v___x_3538_;
v___y_3496_ = v___x_3528_;
v___y_3497_ = v___x_3557_;
v___y_3498_ = v___x_3522_;
v___y_3499_ = v___x_3536_;
v___y_3500_ = v___x_3523_;
v___y_3501_ = v___x_3529_;
v___y_3502_ = v___x_3558_;
v___y_3503_ = v___x_3554_;
v___y_3504_ = v___x_3555_;
v___y_3505_ = v___x_3527_;
v___y_3506_ = v___x_3525_;
v___y_3507_ = v___x_3526_;
v___y_3508_ = v___x_3560_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3561_; 
lean_dec(v___y_3519_);
v___x_3561_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3495_ = v___x_3538_;
v___y_3496_ = v___x_3528_;
v___y_3497_ = v___x_3557_;
v___y_3498_ = v___x_3522_;
v___y_3499_ = v___x_3536_;
v___y_3500_ = v___x_3523_;
v___y_3501_ = v___x_3529_;
v___y_3502_ = v___x_3558_;
v___y_3503_ = v___x_3554_;
v___y_3504_ = v___x_3555_;
v___y_3505_ = v___x_3527_;
v___y_3506_ = v___x_3525_;
v___y_3507_ = v___x_3526_;
v___y_3508_ = v___x_3561_;
goto v___jp_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___boxed(lean_object* v_x_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(v_x_3578_, v_a_3579_, v_a_3580_);
lean_dec_ref(v_a_3579_);
return v_res_3581_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5(void){
_start:
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4));
v___x_3614_ = l_Lean_mkIdent(v___x_3613_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(lean_object* v_x_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3710_; lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = ((lean_object*)(l_Lean_Parser_Tactic_mspec___closed__1));
lean_inc(v_x_3622_);
v___x_3728_ = l_Lean_Syntax_isOfKind(v_x_3622_, v___x_3727_);
if (v___x_3728_ == 0)
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_x_3622_);
v___x_3729_ = lean_box(1);
v___x_3730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v_a_3624_);
return v___x_3730_;
}
else
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_unsigned_to_nat(1u);
v___x_3732_ = l_Lean_Syntax_getArg(v_x_3622_, v___x_3731_);
lean_dec(v_x_3622_);
v___x_3733_ = l_Lean_Syntax_getOptional_x3f(v___x_3732_);
lean_dec(v___x_3732_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_box(0);
v___y_3710_ = v___x_3734_;
goto v___jp_3709_;
}
else
{
lean_object* v_val_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v_val_3735_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3733_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_val_3735_);
lean_dec(v___x_3733_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_val_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
v___y_3710_ = v___x_3740_;
goto v___jp_3709_;
}
}
}
}
v___jp_3625_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_inc_ref_n(v___y_3633_, 2);
v___x_3636_ = l_Array_append___redArg(v___y_3633_, v___y_3635_);
lean_dec_ref(v___y_3635_);
lean_inc_n(v___y_3630_, 12);
lean_inc_n(v___y_3627_, 50);
v___x_3637_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3637_, 0, v___y_3627_);
lean_ctor_set(v___x_3637_, 1, v___y_3630_);
lean_ctor_set(v___x_3637_, 2, v___x_3636_);
lean_inc(v___y_3628_);
v___x_3638_ = l_Lean_Syntax_node2(v___y_3627_, v___y_3628_, v___y_3634_, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3639_, 0, v___y_3627_);
lean_ctor_set(v___x_3639_, 1, v___y_3630_);
lean_ctor_set(v___x_3639_, 2, v___y_3633_);
v___x_3640_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1));
v___x_3641_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2));
v___x_3642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___y_3627_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3644_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3645_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___y_3627_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12));
v___x_3647_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13));
v___x_3648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___y_3627_);
lean_ctor_set(v___x_3648_, 1, v___x_3646_);
v___x_3649_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15));
lean_inc_ref_n(v___x_3639_, 8);
v___x_3650_ = l_Lean_Syntax_node1(v___y_3627_, v___x_3649_, v___x_3639_);
v___x_3651_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17));
v___x_3652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___y_3627_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3630_, v___x_3652_);
v___x_3654_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_3655_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___y_3627_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20));
v___x_3657_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5);
v___x_3658_ = l_Lean_Syntax_node3(v___y_3627_, v___x_3656_, v___x_3639_, v___x_3639_, v___x_3657_);
v___x_3659_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_3660_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___y_3627_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29);
v___x_3662_ = l_Lean_Syntax_node3(v___y_3627_, v___x_3656_, v___x_3639_, v___x_3639_, v___x_3661_);
v___x_3663_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3630_, v___x_3658_, v___x_3660_, v___x_3662_);
v___x_3664_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156));
v___x_3665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___y_3627_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3630_, v___x_3655_, v___x_3663_, v___x_3665_);
v___x_3667_ = l_Lean_Syntax_node6(v___y_3627_, v___x_3647_, v___x_3648_, v___x_3650_, v___x_3639_, v___x_3653_, v___x_3666_, v___x_3639_);
v___x_3668_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3630_, v___x_3667_);
lean_inc_n(v___y_3632_, 7);
v___x_3669_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3668_);
lean_inc_n(v___y_3629_, 7);
v___x_3670_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3669_);
lean_inc_ref(v___x_3645_);
v___x_3671_ = l_Lean_Syntax_node2(v___y_3627_, v___x_3643_, v___x_3645_, v___x_3670_);
v___x_3672_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3630_, v___x_3671_);
v___x_3673_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3672_);
v___x_3674_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3673_);
v___x_3675_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3676_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___y_3627_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
lean_inc_ref_n(v___x_3676_, 3);
lean_inc_n(v___y_3631_, 3);
lean_inc_n(v___y_3626_, 4);
v___x_3677_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3626_, v___y_3631_, v___x_3674_, v___x_3676_);
v___x_3678_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3679_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___y_3627_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = l_Lean_Syntax_node1(v___y_3627_, v___x_3678_, v___x_3680_);
v___x_3682_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___y_3627_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3685_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___y_3627_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = l_Lean_Syntax_node1(v___y_3627_, v___x_3684_, v___x_3686_);
v___x_3688_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3630_, v___x_3681_, v___x_3683_, v___x_3687_);
v___x_3689_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3688_);
v___x_3690_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3689_);
v___x_3691_ = l_Lean_Syntax_node2(v___y_3627_, v___x_3643_, v___x_3645_, v___x_3690_);
v___x_3692_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3630_, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3692_);
v___x_3694_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3693_);
v___x_3695_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3626_, v___y_3631_, v___x_3694_, v___x_3676_);
v___x_3696_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3630_, v___x_3677_, v___x_3639_, v___x_3695_);
v___x_3697_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3696_);
v___x_3698_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3697_);
v___x_3699_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3626_, v___y_3631_, v___x_3698_, v___x_3676_);
v___x_3700_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3630_, v___x_3699_);
v___x_3701_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3700_);
v___x_3702_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3701_);
v___x_3703_ = l_Lean_Syntax_node2(v___y_3627_, v___x_3640_, v___x_3642_, v___x_3702_);
v___x_3704_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3630_, v___x_3638_, v___x_3639_, v___x_3703_);
v___x_3705_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3632_, v___x_3704_);
v___x_3706_ = l_Lean_Syntax_node1(v___y_3627_, v___y_3629_, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node3(v___y_3627_, v___y_3626_, v___y_3631_, v___x_3706_, v___x_3676_);
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v_a_3624_);
return v___x_3708_;
}
v___jp_3709_:
{
lean_object* v_ref_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v_ref_3711_ = lean_ctor_get(v_a_3623_, 5);
v___x_3712_ = 0;
v___x_3713_ = l_Lean_SourceInfo_fromRef(v_ref_3711_, v___x_3712_);
v___x_3714_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3715_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3713_, 2);
v___x_3716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3718_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3719_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3720_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
v___x_3721_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__2));
v___x_3722_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3713_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3710_) == 1)
{
lean_object* v_val_3724_; lean_object* v___x_3725_; 
v_val_3724_ = lean_ctor_get(v___y_3710_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v___y_3710_, 1);
v___x_3725_ = l_Array_mkArray1___redArg(v_val_3724_);
v___y_3626_ = v___x_3714_;
v___y_3627_ = v___x_3713_;
v___y_3628_ = v___x_3720_;
v___y_3629_ = v___x_3717_;
v___y_3630_ = v___x_3719_;
v___y_3631_ = v___x_3716_;
v___y_3632_ = v___x_3718_;
v___y_3633_ = v___x_3723_;
v___y_3634_ = v___x_3722_;
v___y_3635_ = v___x_3725_;
goto v___jp_3625_;
}
else
{
lean_object* v___x_3726_; 
lean_dec(v___y_3710_);
v___x_3726_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3626_ = v___x_3714_;
v___y_3627_ = v___x_3713_;
v___y_3628_ = v___x_3720_;
v___y_3629_ = v___x_3717_;
v___y_3630_ = v___x_3719_;
v___y_3631_ = v___x_3716_;
v___y_3632_ = v___x_3718_;
v___y_3633_ = v___x_3723_;
v___y_3634_ = v___x_3722_;
v___y_3635_ = v___x_3726_;
goto v___jp_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___boxed(lean_object* v_x_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v_res_3746_; 
v_res_3746_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(v_x_3743_, v_a_3744_, v_a_3745_);
lean_dec_ref(v_a_3744_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(lean_object* v_x_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_){
_start:
{
lean_object* v___x_3790_; uint8_t v___x_3791_; 
v___x_3790_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1));
v___x_3791_ = l_Lean_Syntax_isOfKind(v_x_3787_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_box(1);
v___x_3793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set(v___x_3793_, 1, v_a_3789_);
return v___x_3793_;
}
else
{
lean_object* v_ref_3794_; uint8_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v_ref_3794_ = lean_ctor_get(v_a_3788_, 5);
v___x_3795_ = 0;
v___x_3796_ = l_Lean_SourceInfo_fromRef(v_ref_3794_, v___x_3795_);
v___x_3797_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0));
v___x_3798_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1));
lean_inc_n(v___x_3796_, 33);
v___x_3799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3796_);
lean_ctor_set(v___x_3799_, 1, v___x_3797_);
v___x_3800_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3801_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3));
v___x_3802_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4));
v___x_3803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3796_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3805_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3806_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3807_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
v___x_3808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3796_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3810_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3796_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3813_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3796_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3812_, v___x_3814_);
v___x_3816_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3800_, v___x_3815_);
v___x_3817_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3805_, v___x_3816_);
v___x_3818_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3804_, v___x_3817_);
lean_inc_ref(v___x_3811_);
v___x_3819_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3809_, v___x_3811_, v___x_3818_);
v___x_3820_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3800_, v___x_3819_);
v___x_3821_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3805_, v___x_3820_);
v___x_3822_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3804_, v___x_3821_);
v___x_3823_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3824_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3796_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = l_Lean_Syntax_node3(v___x_3796_, v___x_3806_, v___x_3808_, v___x_3822_, v___x_3824_);
v___x_3826_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3796_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3829_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3830_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3796_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3828_, v___x_3830_);
v___x_3832_ = l_Lean_Syntax_node3(v___x_3796_, v___x_3800_, v___x_3825_, v___x_3827_, v___x_3831_);
v___x_3833_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3805_, v___x_3832_);
v___x_3834_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3804_, v___x_3833_);
lean_inc_ref(v___x_3803_);
v___x_3835_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3801_, v___x_3803_, v___x_3834_);
v___x_3836_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1));
v___x_3837_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2));
v___x_3838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3796_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3836_, v___x_3838_);
v___x_3840_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3800_, v___x_3839_);
v___x_3841_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3805_, v___x_3840_);
v___x_3842_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3804_, v___x_3841_);
v___x_3843_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3809_, v___x_3811_, v___x_3842_);
v___x_3844_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3800_, v___x_3843_);
v___x_3845_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3805_, v___x_3844_);
v___x_3846_ = l_Lean_Syntax_node1(v___x_3796_, v___x_3804_, v___x_3845_);
v___x_3847_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3801_, v___x_3803_, v___x_3846_);
v___x_3848_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3800_, v___x_3835_, v___x_3847_);
v___x_3849_ = l_Lean_Syntax_node2(v___x_3796_, v___x_3798_, v___x_3799_, v___x_3848_);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v_a_3789_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___boxed(lean_object* v_x_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(v_x_3851_, v_a_3852_, v_a_3853_);
lean_dec_ref(v_a_3852_);
return v_res_3854_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__4(void){
_start:
{
uint8_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3864_ = 0;
v___x_3865_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__3));
v___x_3866_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__2));
v___x_3867_ = l_Lean_Parser_Tactic_caseArg;
v___x_3868_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v___x_3866_);
lean_ctor_set(v___x_3868_, 2, v___x_3865_);
lean_ctor_set_uint8(v___x_3868_, sizeof(void*)*3, v___x_3864_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__5(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3869_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__4, &l_Lean_Parser_Tactic_vcAlt___closed__4_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__4);
v___x_3870_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__3));
v___x_3871_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3872_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
lean_ctor_set(v___x_3872_, 1, v___x_3870_);
lean_ctor_set(v___x_3872_, 2, v___x_3869_);
return v___x_3872_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__6(void){
_start:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3873_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_3874_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__5, &l_Lean_Parser_Tactic_vcAlt___closed__5_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__5);
v___x_3875_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3876_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set(v___x_3876_, 1, v___x_3874_);
lean_ctor_set(v___x_3876_, 2, v___x_3873_);
return v___x_3876_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__9(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__8));
v___x_3882_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__6, &l_Lean_Parser_Tactic_vcAlt___closed__6_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__6);
v___x_3883_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3884_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
lean_ctor_set(v___x_3884_, 1, v___x_3882_);
lean_ctor_set(v___x_3884_, 2, v___x_3881_);
return v___x_3884_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__10(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3885_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__9, &l_Lean_Parser_Tactic_vcAlt___closed__9_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__9);
v___x_3886_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__1));
v___x_3887_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__0));
v___x_3888_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v___x_3886_);
lean_ctor_set(v___x_3888_, 2, v___x_3885_);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt(void){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__10, &l_Lean_Parser_Tactic_vcAlt___closed__10_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__10);
return v___x_3889_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__15(void){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3924_ = l_Lean_Parser_Tactic_vcAlt;
v___x_3925_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__14));
v___x_3926_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3927_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
lean_ctor_set(v___x_3927_, 1, v___x_3925_);
lean_ctor_set(v___x_3927_, 2, v___x_3924_);
return v___x_3927_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__16(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3928_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__15, &l_Lean_Parser_Tactic_vcAlts___closed__15_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__15);
v___x_3929_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_3930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
lean_ctor_set(v___x_3930_, 1, v___x_3928_);
return v___x_3930_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__17(void){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3931_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__16, &l_Lean_Parser_Tactic_vcAlts___closed__16_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__16);
v___x_3932_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__11));
v___x_3933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3931_);
return v___x_3933_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__18(void){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3934_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__17, &l_Lean_Parser_Tactic_vcAlts___closed__17_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__17);
v___x_3935_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__9));
v___x_3936_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3937_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
lean_ctor_set(v___x_3937_, 1, v___x_3935_);
lean_ctor_set(v___x_3937_, 2, v___x_3934_);
return v___x_3937_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__19(void){
_start:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3938_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__18, &l_Lean_Parser_Tactic_vcAlts___closed__18_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__18);
v___x_3939_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__1));
v___x_3940_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__0));
v___x_3941_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
lean_ctor_set(v___x_3941_, 1, v___x_3939_);
lean_ctor_set(v___x_3941_, 2, v___x_3938_);
return v___x_3941_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts(void){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__19, &l_Lean_Parser_Tactic_vcAlts___closed__19_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__19);
return v___x_3942_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__3(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3952_ = l_Lean_Parser_Tactic_optConfig;
v___x_3953_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__2));
v___x_3954_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3955_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___x_3953_);
lean_ctor_set(v___x_3955_, 2, v___x_3952_);
return v___x_3955_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__10(void){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3965_ = l_Lean_Parser_Tactic_simpLemma;
v___x_3966_ = l_Lean_Parser_Tactic_simpErase;
v___x_3967_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__9));
v___x_3968_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3966_);
lean_ctor_set(v___x_3968_, 2, v___x_3965_);
return v___x_3968_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__11(void){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3969_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__10, &l_Lean_Parser_Tactic_mvcgen___closed__10_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__10);
v___x_3970_ = l_Lean_Parser_Tactic_simpStar;
v___x_3971_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__9));
v___x_3972_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3970_);
lean_ctor_set(v___x_3972_, 2, v___x_3969_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__12(void){
_start:
{
uint8_t v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3973_ = 1;
v___x_3974_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__5));
v___x_3975_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_3976_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__11, &l_Lean_Parser_Tactic_mvcgen___closed__11_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__11);
v___x_3977_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
lean_ctor_set(v___x_3977_, 1, v___x_3975_);
lean_ctor_set(v___x_3977_, 2, v___x_3974_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*3, v___x_3973_);
return v___x_3977_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__13(void){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__12, &l_Lean_Parser_Tactic_mvcgen___closed__12_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__12);
v___x_3979_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__7));
v___x_3980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
lean_ctor_set(v___x_3980_, 1, v___x_3978_);
return v___x_3980_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__14(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3981_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__13, &l_Lean_Parser_Tactic_mvcgen___closed__13_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__13);
v___x_3982_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__5));
v___x_3983_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3984_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3983_);
lean_ctor_set(v___x_3984_, 1, v___x_3982_);
lean_ctor_set(v___x_3984_, 2, v___x_3981_);
return v___x_3984_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__17(void){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__16));
v___x_3989_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__14, &l_Lean_Parser_Tactic_mvcgen___closed__14_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__14);
v___x_3990_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3991_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
lean_ctor_set(v___x_3991_, 1, v___x_3989_);
lean_ctor_set(v___x_3991_, 2, v___x_3988_);
return v___x_3991_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__18(void){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__17, &l_Lean_Parser_Tactic_mvcgen___closed__17_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__17);
v___x_3993_ = ((lean_object*)(l_Lean_Parser_Tactic_mhave___closed__5));
v___x_3994_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
lean_ctor_set(v___x_3994_, 1, v___x_3992_);
return v___x_3994_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__19(void){
_start:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__18, &l_Lean_Parser_Tactic_mvcgen___closed__18_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__18);
v___x_3996_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__3, &l_Lean_Parser_Tactic_mvcgen___closed__3_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__3);
v___x_3997_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_3998_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
lean_ctor_set(v___x_3998_, 1, v___x_3996_);
lean_ctor_set(v___x_3998_, 2, v___x_3995_);
return v___x_3998_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__20(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = l_Lean_Parser_Tactic_invariantAlts;
v___x_4000_ = ((lean_object*)(l_Lean_Parser_Tactic_mhave___closed__5));
v___x_4001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set(v___x_4001_, 1, v___x_3999_);
return v___x_4001_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__21(void){
_start:
{
lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4002_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__20, &l_Lean_Parser_Tactic_mvcgen___closed__20_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__20);
v___x_4003_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__19, &l_Lean_Parser_Tactic_mvcgen___closed__19_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__19);
v___x_4004_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_4005_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v___x_4003_);
lean_ctor_set(v___x_4005_, 2, v___x_4002_);
return v___x_4005_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__22(void){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = l_Lean_Parser_Tactic_vcAlts;
v___x_4007_ = ((lean_object*)(l_Lean_Parser_Tactic_mhave___closed__5));
v___x_4008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
lean_ctor_set(v___x_4008_, 1, v___x_4006_);
return v___x_4008_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__23(void){
_start:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__22, &l_Lean_Parser_Tactic_mvcgen___closed__22_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__22);
v___x_4010_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__21, &l_Lean_Parser_Tactic_mvcgen___closed__21_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__21);
v___x_4011_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_4012_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
lean_ctor_set(v___x_4012_, 1, v___x_4010_);
lean_ctor_set(v___x_4012_, 2, v___x_4009_);
return v___x_4012_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__24(void){
_start:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4013_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__23, &l_Lean_Parser_Tactic_mvcgen___closed__23_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__23);
v___x_4014_ = lean_unsigned_to_nat(1022u);
v___x_4015_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__1));
v___x_4016_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v___x_4014_);
lean_ctor_set(v___x_4016_, 2, v___x_4013_);
return v___x_4016_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen(void){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__24, &l_Lean_Parser_Tactic_mvcgen___closed__24_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__24);
return v___x_4017_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4(void){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4028_ = l_Lean_Parser_Tactic_optConfig;
v___x_4029_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__3));
v___x_4030_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_4031_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v___x_4029_);
lean_ctor_set(v___x_4031_, 2, v___x_4028_);
return v___x_4031_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__18, &l_Lean_Parser_Tactic_mvcgen___closed__18_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__18);
v___x_4033_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__4, &l_Lean_Parser_Tactic_mvcgenHint___closed__4_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4);
v___x_4034_ = ((lean_object*)(l_Lean_Parser_Tactic_mclear___closed__3));
v___x_4035_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v___x_4033_);
lean_ctor_set(v___x_4035_, 2, v___x_4032_);
return v___x_4035_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4036_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__5, &l_Lean_Parser_Tactic_mvcgenHint___closed__5_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5);
v___x_4037_ = lean_unsigned_to_nat(1022u);
v___x_4038_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__1));
v___x_4039_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v___x_4037_);
lean_ctor_set(v___x_4039_, 2, v___x_4036_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint(void){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__6, &l_Lean_Parser_Tactic_mvcgenHint___closed__6_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6);
return v___x_4040_;
}
}
lean_object* runtime_initialize_Std_Do(uint8_t builtin);
lean_object* runtime_initialize_Std_WP_Tactic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Interactive(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_Tactic_mrenameI = _init_l_Lean_Parser_Tactic_mrenameI();
lean_mark_persistent(l_Lean_Parser_Tactic_mrenameI);
l_Lean_Parser_Category_mcasesPat = _init_l_Lean_Parser_Category_mcasesPat();
lean_mark_persistent(l_Lean_Parser_Category_mcasesPat);
l_Lean_Parser_Tactic_mcasesPat__ = _init_l_Lean_Parser_Tactic_mcasesPat__();
lean_mark_persistent(l_Lean_Parser_Tactic_mcasesPat__);
l_Lean_Parser_Tactic_mcasesPat_u231c___u231d = _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d();
lean_mark_persistent(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d);
l_Lean_Parser_Tactic_mcasesPat_u25a1__ = _init_l_Lean_Parser_Tactic_mcasesPat_u25a1__();
lean_mark_persistent(l_Lean_Parser_Tactic_mcasesPat_u25a1__);
l_Lean_Parser_Tactic_mcasesPat_x25__ = _init_l_Lean_Parser_Tactic_mcasesPat_x25__();
lean_mark_persistent(l_Lean_Parser_Tactic_mcasesPat_x25__);
l_Lean_Parser_Tactic_mcasesPat_x23__ = _init_l_Lean_Parser_Tactic_mcasesPat_x23__();
lean_mark_persistent(l_Lean_Parser_Tactic_mcasesPat_x23__);
l_Lean_Parser_Category_mrefinePat = _init_l_Lean_Parser_Category_mrefinePat();
lean_mark_persistent(l_Lean_Parser_Category_mrefinePat);
l_Lean_Parser_Tactic_mrefinePat__ = _init_l_Lean_Parser_Tactic_mrefinePat__();
lean_mark_persistent(l_Lean_Parser_Tactic_mrefinePat__);
l_Lean_Parser_Tactic_mrefinePat_u25a1__ = _init_l_Lean_Parser_Tactic_mrefinePat_u25a1__();
lean_mark_persistent(l_Lean_Parser_Tactic_mrefinePat_u25a1__);
l_Lean_Parser_Tactic_mrefinePat_x3f__ = _init_l_Lean_Parser_Tactic_mrefinePat_x3f__();
lean_mark_persistent(l_Lean_Parser_Tactic_mrefinePat_x3f__);
l_Lean_Parser_Tactic_mrefinePat_x23__ = _init_l_Lean_Parser_Tactic_mrefinePat_x23__();
lean_mark_persistent(l_Lean_Parser_Tactic_mrefinePat_x23__);
l_Lean_Parser_Category_mintroPat = _init_l_Lean_Parser_Category_mintroPat();
lean_mark_persistent(l_Lean_Parser_Category_mintroPat);
l_Lean_Parser_Tactic_mintroPat_u2200__ = _init_l_Lean_Parser_Tactic_mintroPat_u2200__();
lean_mark_persistent(l_Lean_Parser_Tactic_mintroPat_u2200__);
l_Lean_Parser_Category_mrevertPat = _init_l_Lean_Parser_Category_mrevertPat();
lean_mark_persistent(l_Lean_Parser_Category_mrevertPat);
l_Lean_Parser_Tactic_vcAlt = _init_l_Lean_Parser_Tactic_vcAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_vcAlt);
l_Lean_Parser_Tactic_vcAlts = _init_l_Lean_Parser_Tactic_vcAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_vcAlts);
l_Lean_Parser_Tactic_mvcgen = _init_l_Lean_Parser_Tactic_mvcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_mvcgen);
l_Lean_Parser_Tactic_mvcgenHint = _init_l_Lean_Parser_Tactic_mvcgenHint();
lean_mark_persistent(l_Lean_Parser_Tactic_mvcgenHint);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do(uint8_t builtin);
lean_object* initialize_Std_WP_Tactic(uint8_t builtin);
lean_object* initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
lean_object* initialize_Init_Grind_Interactive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_WP_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Interactive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_Do_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
