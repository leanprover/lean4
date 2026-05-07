// Lean compiler output
// Module: Std.Tactic.Do.Syntax
// Imports: public import Std.Do public import Std.Tactic.Do.ProofMode public import Init.Data.Array.GetLit
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
extern lean_object* l_Lean_cdotTk;
lean_object* lean_mk_syntax_ident(lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
extern lean_object* l_Lean_binderIdent;
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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lean_Parser_Attr_spec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__0 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__1 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__2 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__2_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "spec"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__3 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Attr_spec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 37, 203, 230, 106, 254, 64, 102)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__4 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__5 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__6 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__7 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__7_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__8 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__8_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__9 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__10 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__10_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__11 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__11_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__12 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value;
static const lean_string_object l_Lean_Parser_Attr_spec___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prio"};
static const lean_object* l_Lean_Parser_Attr_spec___closed__13 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__13_value),LEAN_SCALAR_PTR_LITERAL(122, 247, 65, 238, 243, 154, 137, 247)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__14 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__15 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__15_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__16 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__16_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__17 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__7_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__17_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__18 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Attr_spec___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__4_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__18_value)}};
static const lean_object* l_Lean_Parser_Attr_spec___closed__19 = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Attr_spec = (const lean_object*)&l_Lean_Parser_Attr_spec___closed__19_value;
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value;
static const lean_string_object l_Lean_Parser_Tactic_massumption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "massumption"};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 248, 144, 74, 231, 227, 47, 25)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_massumption___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_massumption___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_massumption = (const lean_object*)&l_Lean_Parser_Tactic_massumption___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mclear"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 161, 32, 25, 224, 212, 229, 174)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__3_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mclear___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__7_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclear___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclear___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mclear = (const lean_object*)&l_Lean_Parser_Tactic_mclear___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic_mclearError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mclearError"};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 218, 126, 93, 176, 59, 180, 45)}};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mclearError___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mclearError___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mclearError = (const lean_object*)&l_Lean_Parser_Tactic_mclearError___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`mclear` expects at an identifier"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mconstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mconstructor"};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 154, 195, 216, 142, 75, 110, 212)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mconstructor___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mconstructor___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mconstructor = (const lean_object*)&l_Lean_Parser_Tactic_mconstructor___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexact___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mexact"};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 177, 11, 252, 148, 218, 54, 90)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexact___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__4_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexact___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexact___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexact = (const lean_object*)&l_Lean_Parser_Tactic_mexact___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mexactError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mexactError"};
static const lean_object* l_Lean_Parser_Tactic_mexactError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexactError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 221, 191, 226, 253, 105, 73, 187)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexfalso___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexfalso___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexfalso = (const lean_object*)&l_Lean_Parser_Tactic_mexfalso___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mexists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mexists"};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexists___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mexists___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mexists = (const lean_object*)&l_Lean_Parser_Tactic_mexists___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mexistsError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mexistsError"};
static const lean_object* l_Lean_Parser_Tactic_mexistsError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexistsError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 145, 19, 234, 215, 109, 237, 186)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mframe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mframe___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mframe___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mframe = (const lean_object*)&l_Lean_Parser_Tactic_mframe___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mdup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mdup"};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 112, 88, 152, 42, 238, 157, 119)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mdup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mdup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mdup___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mdup = (const lean_object*)&l_Lean_Parser_Tactic_mdup___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mhave"};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 47, 33, 106, 233, 48, 163, 59)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mhave___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhave___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mhave___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mhave = (const lean_object*)&l_Lean_Parser_Tactic_mhave___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic_mhaveError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mhaveError"};
static const lean_object* l_Lean_Parser_Tactic_mhaveError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mhaveError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(179, 100, 86, 218, 99, 164, 72, 83)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mhave___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplace___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mreplace___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mreplace = (const lean_object*)&l_Lean_Parser_Tactic_mreplace___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mreplaceError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mreplaceError"};
static const lean_object* l_Lean_Parser_Tactic_mreplaceError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mreplaceError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mright___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 16, 212, 5, 110, 91, 32)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mright___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mright___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mright___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mright___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mright = (const lean_object*)&l_Lean_Parser_Tactic_mright___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mleft___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mleft"};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 82, 79, 80, 116, 5, 61, 30)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleft___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mleft___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mleft___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mleft = (const lean_object*)&l_Lean_Parser_Tactic_mleft___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mpure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mpure"};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 40, 78, 170, 57, 132, 109, 163)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mpure___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mpure___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mpure = (const lean_object*)&l_Lean_Parser_Tactic_mpure___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mpureError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mpureError"};
static const lean_object* l_Lean_Parser_Tactic_mpureError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mpureIntro___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameI___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Attr_spec___closed__12_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrenameI___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_mrenameI___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrenameI___closed__10;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrenameI;
static const lean_string_object l_Lean_Parser_Tactic_mrenameIError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mrenameIError"};
static const lean_object* l_Lean_Parser_Tactic_mrenameIError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameIError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 227, 189, 220, 199, 75, 123, 209)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecialize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__5_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecialize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecialize___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecialize = (const lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializeError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mspecializeError"};
static const lean_object* l_Lean_Parser_Tactic_mspecializeError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializeError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 62, 145, 88, 202, 28, 127)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializePure___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mspecialize_pure"};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mdup___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePure___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecializePure___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecializePure = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePure___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecializePureError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "mspecializePureError"};
static const lean_object* l_Lean_Parser_Tactic_mspecializePureError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecializePureError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 72, 234, 250, 239, 149, 139, 165)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mstart___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mstart___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mstart = (const lean_object*)&l_Lean_Parser_Tactic_mstart___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mstop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mstop"};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 209, 80, 25, 253, 26, 68, 170)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mstop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mstop___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mstop___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mstop = (const lean_object*)&l_Lean_Parser_Tactic_mstop___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mleave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mleave"};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 47, 148, 137, 18, 118, 104, 201)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mleave___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mleave___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mleave___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mleave = (const lean_object*)&l_Lean_Parser_Tactic_mleave___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__157_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__160_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mcasesPat;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mcasesPatAlts"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPatAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 196, 52, 121, 17, 165, 127, 126)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mcasesPat___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mcasesPat___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mcasesPat__;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mcasesPat-"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 121, 122, 163, 184, 200, 40, 28)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__9_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mcasesPat(_)"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 228, 45, 90, 25, 77, 183, 251)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPatAlts___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcasesPat_x28___x29 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 12, .m_data = "mcasesPat⌜_⌝"};
static const lean_object* l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 192, 12, 149, 146, 251, 197, 23)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mcases___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcases___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mcases___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mcases = (const lean_object*)&l_Lean_Parser_Tactic_mcases___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_mcasesError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mcasesError"};
static const lean_object* l_Lean_Parser_Tactic_mcasesError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mrefinePat;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePat_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 205, 252, 11, 203, 77, 12, 3)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat__;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrefinePats"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value),LEAN_SCALAR_PTR_LITERAL(112, 173, 91, 190, 46, 156, 169, 121)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePats___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePats___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePats = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⟨_⟩"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 252, 110, 106, 145, 210, 7, 196)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePats___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mrefinePat(_)"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__0_value),LEAN_SCALAR_PTR_LITERAL(145, 235, 27, 55, 120, 135, 13, 209)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_x28___x29 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "mrefinePat⌜_⌝"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 247, 138, 95, 101, 152, 141, 145)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_u231c___u231d = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrefinePat□_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 27, 205, 29, 81, 36, 207, 246)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat_u25a1__;
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat\?_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 246, 182, 233, 244, 232, 234, 234)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefinePat_x25__ = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefinePat#_"};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 43, 185, 96, 20, 2, 38, 80)}};
static const lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mrefinePat_x23__;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 147, 116, 116, 185, 89, 229, 87)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrefinePat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefine___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrefine___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrefine = (const lean_object*)&l_Lean_Parser_Tactic_mrefine___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_mrefineError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrefineError"};
static const lean_object* l_Lean_Parser_Tactic_mrefineError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrefineError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintroPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mintroPat;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mintroPat_"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(23, 197, 23, 48, 210, 183, 157, 165)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintroPat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintroPat__ = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "mintroPat∀_"};
static const lean_object* l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 222, 62, 246, 205, 225, 8, 203)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintro___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mintro___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mintro___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mintro = (const lean_object*)&l_Lean_Parser_Tactic_mintro___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mintroError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mintroError"};
static const lean_object* l_Lean_Parser_Tactic_mintroError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mintroError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat_quot = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_mrevertPat;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mrevertPat_"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(237, 56, 253, 143, 81, 27, 28, 109)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat__ = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat___00__closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 12, .m_data = "mrevertPat∀_"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 101, 4, 189, 225, 175, 44, 14)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevertPat_u2200__ = (const lean_object*)&l_Lean_Parser_Tactic_mrevertPat_u2200___00__closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mrevert"};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(82, 105, 168, 208, 87, 76, 255, 172)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrevertPat_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecialize___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mrevert___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mrevert = (const lean_object*)&l_Lean_Parser_Tactic_mrevert___closed__6_value;
static const lean_string_object l_Lean_Parser_Tactic_mrevertError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mrevertError"};
static const lean_object* l_Lean_Parser_Tactic_mrevertError___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mrevertError___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 86, 213, 46, 163, 23, 151, 189)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoBind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mspec_no_bind"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoBind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoBind___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecNoBind = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "mspecNoSimp"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 95, 246, 218, 2, 114, 192, 99)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mspec_no_simp"};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspecNoSimp___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspecNoSimp = (const lean_object*)&l_Lean_Parser_Tactic_mspecNoSimp___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 251, 147, 100, 37, 246, 67, 31)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__2_value),((lean_object*)&l_Lean_Parser_Tactic_mspecNoBind___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mspec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_mspec___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_mspec___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_mspec = (const lean_object*)&l_Lean_Parser_Tactic_mspec___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "allGoals"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(91, 113, 211, 1, 53, 106, 100, 38)}};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7_value;
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "tacticMvcgen_trivial_extensible"};
static const lean_object* l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__8;
static const lean_string_object l_Lean_Parser_Tactic_invariantDotAlt___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__9_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__10_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantDotAlt___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__11_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__12_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantDotAlt___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantDotAlt___closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantDotAlt;
static const lean_string_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantDotAlt___closed__7_value),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__3_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantCaseAlt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantCaseAlt___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantCaseAlt;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariantsKW"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 87, 251, 76, 123, 116, 93, 232)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__3_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "invariants "};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),LEAN_SCALAR_PTR_LITERAL(252, 45, 21, 37, 250, 87, 14, 102)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__8_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantsKW___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariants\? "};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__5_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),LEAN_SCALAR_PTR_LITERAL(241, 40, 134, 186, 103, 193, 43, 220)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__10_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__11_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__12 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__8_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__12_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantsKW___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__0_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__1_value),((lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_invariantsKW___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_invariantsKW = (const lean_object*)&l_Lean_Parser_Tactic_invariantsKW___closed__14_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_invariantAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_invariantAlts___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_invariantAlts___closed__3_value;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_invariantAlts___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_invariantAlts___closed__9;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_invariantAlts;
static const lean_string_object l_Lean_Parser_Tactic_vcAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcAlt"};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 45, 84, 214, 166, 18, 7, 59)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__2;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__4;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlt___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlt___closed__6_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__7;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlt___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlt___closed__8;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcAlt;
static const lean_string_object l_Lean_Parser_Tactic_vcAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "vcAlts"};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcAlts___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcAlts___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__9_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_vcAlts___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcAlts___closed__14;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcAlts;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__8;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__9;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__10;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__11;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__12;
static const lean_string_object l_Lean_Parser_Tactic_mvcgen___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "] "};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__13 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgen___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__13_value)}};
static const lean_object* l_Lean_Parser_Tactic_mvcgen___closed__14 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__14_value;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_mvcgen___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_mvcgen___closed__16;
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_mvcgen;
static const lean_string_object l_Lean_Parser_Tactic_mvcgenHint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "mvcgenHint"};
static const lean_object* l_Lean_Parser_Tactic_mvcgenHint___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mvcgenHint___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(lean_object* v_x_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = ((lean_object*)(l_Lean_Parser_Tactic_mclearError___closed__1));
v___x_109_ = l_Lean_Syntax_isOfKind(v_x_105_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_box(1);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_107_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0));
v___x_113_ = l_Lean_Macro_throwError___redArg(v___x_112_, v_a_106_, v_a_107_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_a_115_ = lean_ctor_get(v___x_113_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_113_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_114_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
v_a_123_ = lean_ctor_get(v___x_113_, 0);
v_a_124_ = lean_ctor_get(v___x_113_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_113_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_inc(v_a_123_);
lean_dec(v___x_113_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_123_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1(v_x_132_, v_a_133_, v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1(lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Parser_Tactic_mexactError___closed__1));
v___x_194_ = l_Lean_Syntax_isOfKind(v_x_190_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(1);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_192_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___closed__0));
v___x_198_ = l_Lean_Macro_throwError___redArg(v___x_197_, v_a_191_, v_a_192_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_a_200_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_198_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_199_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_a_208_; lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_208_ = lean_ctor_get(v___x_198_, 0);
v_a_209_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_198_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_inc(v_a_208_);
lean_dec(v___x_198_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_208_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1___boxed(lean_object* v_x_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexactError__1(v_x_217_, v_a_218_, v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1(lean_object* v_x_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Parser_Tactic_mexistsError___closed__1));
v___x_278_ = l_Lean_Syntax_isOfKind(v_x_274_, v___x_277_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(1);
v___x_280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_a_276_);
return v___x_280_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___closed__0));
v___x_282_ = l_Lean_Macro_throwError___redArg(v___x_281_, v_a_275_, v_a_276_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_a_284_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_282_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_a_292_; lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
v_a_292_ = lean_ctor_get(v___x_282_, 0);
v_a_293_ = lean_ctor_get(v___x_282_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_282_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_inc(v_a_292_);
lean_dec(v___x_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_292_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1___boxed(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mexistsError__1(v_x_301_, v_a_302_, v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1(lean_object* v_x_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Parser_Tactic_mhaveError___closed__1));
v___x_407_ = l_Lean_Syntax_isOfKind(v_x_403_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_box(1);
v___x_409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_a_405_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___closed__0));
v___x_411_ = l_Lean_Macro_throwError___redArg(v___x_410_, v_a_404_, v_a_405_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_a_413_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_411_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_412_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
else
{
lean_object* v_a_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_421_ = lean_ctor_get(v___x_411_, 0);
v_a_422_ = lean_ctor_get(v___x_411_, 1);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_inc(v_a_421_);
lean_dec(v___x_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_421_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1___boxed(lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mhaveError__1(v_x_430_, v_a_431_, v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1(lean_object* v_x_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Parser_Tactic_mreplaceError___closed__1));
v___x_480_ = l_Lean_Syntax_isOfKind(v_x_476_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_box(1);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_a_478_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___closed__0));
v___x_484_ = l_Lean_Macro_throwError___redArg(v___x_483_, v_a_477_, v_a_478_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_a_486_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_484_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_485_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
else
{
lean_object* v_a_494_; lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
v_a_494_ = lean_ctor_get(v___x_484_, 0);
v_a_495_ = lean_ctor_get(v___x_484_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_484_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_inc(v_a_494_);
lean_dec(v___x_484_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_494_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1___boxed(lean_object* v_x_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mreplaceError__1(v_x_503_, v_a_504_, v_a_505_);
lean_dec_ref(v_a_504_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1(lean_object* v_x_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_572_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureError___closed__1));
v___x_573_ = l_Lean_Syntax_isOfKind(v_x_569_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_box(1);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_574_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
return v___x_575_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___closed__0));
v___x_577_ = l_Lean_Macro_throwError___redArg(v___x_576_, v_a_570_, v_a_571_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_a_579_ = lean_ctor_get(v___x_577_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_577_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_578_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_587_ = lean_ctor_get(v___x_577_, 0);
v_a_588_ = lean_ctor_get(v___x_577_, 1);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_577_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_inc(v_a_587_);
lean_dec(v___x_577_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_587_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1___boxed(lean_object* v_x_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mpureError__1(v_x_596_, v_a_597_, v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_599_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__7(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = l_Lean_binderIdent;
v___x_633_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__6));
v___x_634_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_635_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__8(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__7, &l_Lean_Parser_Tactic_mrenameI___closed__7_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__7);
v___x_637_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__5));
v___x_638_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__9(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__8, &l_Lean_Parser_Tactic_mrenameI___closed__8_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__8);
v___x_640_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__3));
v___x_641_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_642_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
lean_ctor_set(v___x_642_, 1, v___x_640_);
lean_ctor_set(v___x_642_, 2, v___x_639_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI___closed__10(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_643_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__9, &l_Lean_Parser_Tactic_mrenameI___closed__9_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__9);
v___x_644_ = lean_unsigned_to_nat(1022u);
v___x_645_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__1));
v___x_646_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_643_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrenameI(void){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__10, &l_Lean_Parser_Tactic_mrenameI___closed__10_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__10);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1(lean_object* v_x_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameIError___closed__1));
v___x_664_ = l_Lean_Syntax_isOfKind(v_x_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_box(1);
v___x_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_a_662_);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___closed__0));
v___x_668_ = l_Lean_Macro_throwError___redArg(v___x_667_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
v_a_670_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_668_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_inc(v_a_669_);
lean_dec(v___x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_669_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_678_ = lean_ctor_get(v___x_668_, 0);
v_a_679_ = lean_ctor_get(v___x_668_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_668_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_inc(v_a_678_);
lean_dec(v___x_668_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_678_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1___boxed(lean_object* v_x_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrenameIError__1(v_x_687_, v_a_688_, v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1(lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecializeError___closed__1));
v___x_742_ = l_Lean_Syntax_isOfKind(v_x_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_box(1);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_a_740_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___closed__0));
v___x_746_ = l_Lean_Macro_throwError___redArg(v___x_745_, v_a_739_, v_a_740_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_a_748_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_747_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_a_756_ = lean_ctor_get(v___x_746_, 0);
v_a_757_ = lean_ctor_get(v___x_746_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_746_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_inc(v_a_756_);
lean_dec(v___x_746_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1___boxed(lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializeError__1(v_x_765_, v_a_766_, v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1(lean_object* v_x_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecializePureError___closed__1));
v___x_816_ = l_Lean_Syntax_isOfKind(v_x_812_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_box(1);
v___x_818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v_a_814_);
return v___x_818_;
}
else
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___closed__0));
v___x_820_ = l_Lean_Macro_throwError___redArg(v___x_819_, v_a_813_, v_a_814_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_a_822_ = lean_ctor_get(v___x_820_, 1);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_820_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
else
{
lean_object* v_a_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
v_a_830_ = lean_ctor_get(v___x_820_, 0);
v_a_831_ = lean_ctor_get(v___x_820_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_820_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_inc(v_a_830_);
lean_dec(v___x_820_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_830_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1___boxed(lean_object* v_x_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecializePureError__1(v_x_839_, v_a_840_, v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_842_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16(void){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Array_mkArray0(lean_box(0));
return v___x_926_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__25));
v___x_945_ = lean_mk_syntax_ident(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28));
v___x_953_ = lean_mk_syntax_ident(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31));
v___x_961_ = lean_mk_syntax_ident(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34));
v___x_969_ = lean_mk_syntax_ident(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37));
v___x_977_ = lean_mk_syntax_ident(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40));
v___x_985_ = lean_mk_syntax_ident(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43));
v___x_993_ = lean_mk_syntax_ident(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46));
v___x_1001_ = lean_mk_syntax_ident(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49));
v___x_1009_ = lean_mk_syntax_ident(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52));
v___x_1017_ = lean_mk_syntax_ident(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55));
v___x_1025_ = lean_mk_syntax_ident(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58));
v___x_1033_ = lean_mk_syntax_ident(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61));
v___x_1041_ = lean_mk_syntax_ident(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64));
v___x_1049_ = lean_mk_syntax_ident(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67));
v___x_1057_ = lean_mk_syntax_ident(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70));
v___x_1065_ = lean_mk_syntax_ident(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73));
v___x_1073_ = lean_mk_syntax_ident(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76));
v___x_1081_ = lean_mk_syntax_ident(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79));
v___x_1089_ = lean_mk_syntax_ident(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82));
v___x_1097_ = lean_mk_syntax_ident(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85));
v___x_1105_ = lean_mk_syntax_ident(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88));
v___x_1113_ = lean_mk_syntax_ident(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92));
v___x_1122_ = lean_mk_syntax_ident(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95));
v___x_1130_ = lean_mk_syntax_ident(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98));
v___x_1138_ = lean_mk_syntax_ident(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101));
v___x_1146_ = lean_mk_syntax_ident(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104));
v___x_1154_ = lean_mk_syntax_ident(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107));
v___x_1162_ = lean_mk_syntax_ident(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112));
v___x_1173_ = lean_mk_syntax_ident(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115));
v___x_1181_ = lean_mk_syntax_ident(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118));
v___x_1189_ = lean_mk_syntax_ident(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122));
v___x_1196_ = lean_mk_syntax_ident(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125));
v___x_1202_ = lean_mk_syntax_ident(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130));
v___x_1211_ = lean_mk_syntax_ident(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133));
v___x_1218_ = lean_mk_syntax_ident(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136));
v___x_1225_ = lean_mk_syntax_ident(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139));
v___x_1232_ = lean_mk_syntax_ident(v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142));
v___x_1237_ = lean_mk_syntax_ident(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145));
v___x_1242_ = lean_mk_syntax_ident(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148));
v___x_1247_ = lean_mk_syntax_ident(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151));
v___x_1252_ = lean_mk_syntax_ident(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154));
v___x_1257_ = lean_mk_syntax_ident(v___x_1256_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1(lean_object* v_x_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_Parser_Tactic_mleave___closed__1));
v___x_1278_ = l_Lean_Syntax_isOfKind(v_x_1274_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_box(1);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_a_1276_);
return v___x_1280_;
}
else
{
lean_object* v_ref_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v_ref_1281_ = lean_ctor_get(v_a_1275_, 5);
v___x_1282_ = 0;
v___x_1283_ = l_Lean_SourceInfo_fromRef(v_ref_1281_, v___x_1282_);
v___x_1284_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_1285_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_1283_, 68);
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1283_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_1288_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_1289_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_1290_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_1291_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_1292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1283_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12));
v___x_1294_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13));
v___x_1295_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1283_);
lean_ctor_set(v___x_1295_, 1, v___x_1293_);
v___x_1296_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15));
v___x_1297_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
v___x_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1283_);
lean_ctor_set(v___x_1298_, 1, v___x_1289_);
lean_ctor_set(v___x_1298_, 2, v___x_1297_);
lean_inc_ref_n(v___x_1298_, 85);
v___x_1299_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1296_, v___x_1298_);
v___x_1300_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17));
v___x_1301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1283_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1289_, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_1304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1283_);
lean_ctor_set(v___x_1304_, 1, v___x_1303_);
v___x_1305_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20));
v___x_1306_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__26);
v___x_1307_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1306_);
v___x_1308_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_1309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1283_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29);
v___x_1311_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1310_);
v___x_1312_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32);
v___x_1313_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1312_);
v___x_1314_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35);
v___x_1315_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1314_);
v___x_1316_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38);
v___x_1317_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1316_);
v___x_1318_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41);
v___x_1319_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44);
v___x_1321_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1320_);
v___x_1322_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47);
v___x_1323_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1322_);
v___x_1324_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50);
v___x_1325_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1324_);
v___x_1326_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53);
v___x_1327_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56);
v___x_1329_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1328_);
v___x_1330_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59);
v___x_1331_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1330_);
v___x_1332_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62);
v___x_1333_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1332_);
v___x_1334_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65);
v___x_1335_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1334_);
v___x_1336_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68);
v___x_1337_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1336_);
v___x_1338_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71);
v___x_1339_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74);
v___x_1341_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1340_);
v___x_1342_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77);
v___x_1343_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80);
v___x_1345_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83);
v___x_1347_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1346_);
v___x_1348_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86);
v___x_1349_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1348_);
v___x_1350_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89);
v___x_1351_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93);
v___x_1353_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96);
v___x_1355_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99);
v___x_1357_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1356_);
v___x_1358_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102);
v___x_1359_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1358_);
v___x_1360_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105);
v___x_1361_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108);
v___x_1363_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1362_);
v___x_1364_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113);
v___x_1365_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116);
v___x_1367_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1366_);
v___x_1368_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119);
v___x_1369_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123);
v___x_1371_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1370_);
v___x_1372_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126);
v___x_1373_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131);
v___x_1375_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1374_);
v___x_1376_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134);
v___x_1377_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1376_);
v___x_1378_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137);
v___x_1379_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1378_);
v___x_1380_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140);
v___x_1381_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1380_);
v___x_1382_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143);
v___x_1383_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1382_);
v___x_1384_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146);
v___x_1385_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1384_);
v___x_1386_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149);
v___x_1387_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1386_);
v___x_1388_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152);
v___x_1389_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1388_);
v___x_1390_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155);
v___x_1391_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1305_, v___x_1298_, v___x_1298_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(83u);
v___x_1393_ = lean_mk_empty_array_with_capacity(v___x_1392_);
v___x_1394_ = lean_array_push(v___x_1393_, v___x_1307_);
lean_inc_ref_n(v___x_1309_, 40);
v___x_1395_ = lean_array_push(v___x_1394_, v___x_1309_);
v___x_1396_ = lean_array_push(v___x_1395_, v___x_1311_);
v___x_1397_ = lean_array_push(v___x_1396_, v___x_1309_);
v___x_1398_ = lean_array_push(v___x_1397_, v___x_1313_);
v___x_1399_ = lean_array_push(v___x_1398_, v___x_1309_);
v___x_1400_ = lean_array_push(v___x_1399_, v___x_1315_);
v___x_1401_ = lean_array_push(v___x_1400_, v___x_1309_);
v___x_1402_ = lean_array_push(v___x_1401_, v___x_1317_);
v___x_1403_ = lean_array_push(v___x_1402_, v___x_1309_);
v___x_1404_ = lean_array_push(v___x_1403_, v___x_1319_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1309_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1321_);
v___x_1407_ = lean_array_push(v___x_1406_, v___x_1309_);
v___x_1408_ = lean_array_push(v___x_1407_, v___x_1323_);
v___x_1409_ = lean_array_push(v___x_1408_, v___x_1309_);
v___x_1410_ = lean_array_push(v___x_1409_, v___x_1325_);
v___x_1411_ = lean_array_push(v___x_1410_, v___x_1309_);
v___x_1412_ = lean_array_push(v___x_1411_, v___x_1327_);
v___x_1413_ = lean_array_push(v___x_1412_, v___x_1309_);
v___x_1414_ = lean_array_push(v___x_1413_, v___x_1329_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1309_);
v___x_1416_ = lean_array_push(v___x_1415_, v___x_1331_);
v___x_1417_ = lean_array_push(v___x_1416_, v___x_1309_);
v___x_1418_ = lean_array_push(v___x_1417_, v___x_1333_);
v___x_1419_ = lean_array_push(v___x_1418_, v___x_1309_);
v___x_1420_ = lean_array_push(v___x_1419_, v___x_1335_);
v___x_1421_ = lean_array_push(v___x_1420_, v___x_1309_);
v___x_1422_ = lean_array_push(v___x_1421_, v___x_1337_);
v___x_1423_ = lean_array_push(v___x_1422_, v___x_1309_);
v___x_1424_ = lean_array_push(v___x_1423_, v___x_1339_);
v___x_1425_ = lean_array_push(v___x_1424_, v___x_1309_);
v___x_1426_ = lean_array_push(v___x_1425_, v___x_1341_);
v___x_1427_ = lean_array_push(v___x_1426_, v___x_1309_);
v___x_1428_ = lean_array_push(v___x_1427_, v___x_1343_);
v___x_1429_ = lean_array_push(v___x_1428_, v___x_1309_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1345_);
v___x_1431_ = lean_array_push(v___x_1430_, v___x_1309_);
v___x_1432_ = lean_array_push(v___x_1431_, v___x_1347_);
v___x_1433_ = lean_array_push(v___x_1432_, v___x_1309_);
v___x_1434_ = lean_array_push(v___x_1433_, v___x_1349_);
v___x_1435_ = lean_array_push(v___x_1434_, v___x_1309_);
v___x_1436_ = lean_array_push(v___x_1435_, v___x_1351_);
v___x_1437_ = lean_array_push(v___x_1436_, v___x_1309_);
v___x_1438_ = lean_array_push(v___x_1437_, v___x_1353_);
v___x_1439_ = lean_array_push(v___x_1438_, v___x_1309_);
v___x_1440_ = lean_array_push(v___x_1439_, v___x_1355_);
v___x_1441_ = lean_array_push(v___x_1440_, v___x_1309_);
v___x_1442_ = lean_array_push(v___x_1441_, v___x_1357_);
v___x_1443_ = lean_array_push(v___x_1442_, v___x_1309_);
v___x_1444_ = lean_array_push(v___x_1443_, v___x_1359_);
v___x_1445_ = lean_array_push(v___x_1444_, v___x_1309_);
v___x_1446_ = lean_array_push(v___x_1445_, v___x_1361_);
v___x_1447_ = lean_array_push(v___x_1446_, v___x_1309_);
v___x_1448_ = lean_array_push(v___x_1447_, v___x_1363_);
v___x_1449_ = lean_array_push(v___x_1448_, v___x_1309_);
v___x_1450_ = lean_array_push(v___x_1449_, v___x_1365_);
v___x_1451_ = lean_array_push(v___x_1450_, v___x_1309_);
v___x_1452_ = lean_array_push(v___x_1451_, v___x_1367_);
v___x_1453_ = lean_array_push(v___x_1452_, v___x_1309_);
v___x_1454_ = lean_array_push(v___x_1453_, v___x_1369_);
v___x_1455_ = lean_array_push(v___x_1454_, v___x_1309_);
v___x_1456_ = lean_array_push(v___x_1455_, v___x_1371_);
v___x_1457_ = lean_array_push(v___x_1456_, v___x_1309_);
v___x_1458_ = lean_array_push(v___x_1457_, v___x_1373_);
v___x_1459_ = lean_array_push(v___x_1458_, v___x_1309_);
v___x_1460_ = lean_array_push(v___x_1459_, v___x_1375_);
v___x_1461_ = lean_array_push(v___x_1460_, v___x_1309_);
v___x_1462_ = lean_array_push(v___x_1461_, v___x_1377_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1309_);
v___x_1464_ = lean_array_push(v___x_1463_, v___x_1379_);
v___x_1465_ = lean_array_push(v___x_1464_, v___x_1309_);
v___x_1466_ = lean_array_push(v___x_1465_, v___x_1381_);
v___x_1467_ = lean_array_push(v___x_1466_, v___x_1309_);
v___x_1468_ = lean_array_push(v___x_1467_, v___x_1383_);
v___x_1469_ = lean_array_push(v___x_1468_, v___x_1309_);
v___x_1470_ = lean_array_push(v___x_1469_, v___x_1385_);
v___x_1471_ = lean_array_push(v___x_1470_, v___x_1309_);
v___x_1472_ = lean_array_push(v___x_1471_, v___x_1387_);
v___x_1473_ = lean_array_push(v___x_1472_, v___x_1309_);
v___x_1474_ = lean_array_push(v___x_1473_, v___x_1389_);
v___x_1475_ = lean_array_push(v___x_1474_, v___x_1309_);
v___x_1476_ = lean_array_push(v___x_1475_, v___x_1391_);
v___x_1477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1283_);
lean_ctor_set(v___x_1477_, 1, v___x_1289_);
lean_ctor_set(v___x_1477_, 2, v___x_1476_);
v___x_1478_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156));
v___x_1479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1283_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
v___x_1480_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1289_, v___x_1304_, v___x_1477_, v___x_1479_);
v___x_1481_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__158));
v___x_1482_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__159));
v___x_1483_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1283_);
lean_ctor_set(v___x_1483_, 1, v___x_1482_);
v___x_1484_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__161));
v___x_1485_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__162));
v___x_1486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1283_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1484_, v___x_1486_);
v___x_1488_ = l_Lean_Syntax_node2(v___x_1283_, v___x_1481_, v___x_1483_, v___x_1487_);
v___x_1489_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1289_, v___x_1488_);
v___x_1490_ = l_Lean_Syntax_node6(v___x_1283_, v___x_1294_, v___x_1295_, v___x_1299_, v___x_1298_, v___x_1302_, v___x_1480_, v___x_1489_);
v___x_1491_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1289_, v___x_1490_);
v___x_1492_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1288_, v___x_1491_);
v___x_1493_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1287_, v___x_1492_);
v___x_1494_ = l_Lean_Syntax_node2(v___x_1283_, v___x_1290_, v___x_1292_, v___x_1493_);
v___x_1495_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1289_, v___x_1494_);
v___x_1496_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1288_, v___x_1495_);
v___x_1497_ = l_Lean_Syntax_node1(v___x_1283_, v___x_1287_, v___x_1496_);
v___x_1498_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_1499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1283_);
lean_ctor_set(v___x_1499_, 1, v___x_1498_);
v___x_1500_ = l_Lean_Syntax_node3(v___x_1283_, v___x_1284_, v___x_1286_, v___x_1497_, v___x_1499_);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
lean_ctor_set(v___x_1501_, 1, v_a_1276_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___boxed(lean_object* v_x_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1(v_x_1502_, v_a_1503_, v_a_1504_);
lean_dec_ref(v_a_1503_);
return v_res_1505_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mcasesPat(void){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_box(0);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat___00__closed__2(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1570_ = l_Lean_binderIdent;
v___x_1571_ = lean_unsigned_to_nat(1022u);
v___x_1572_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
v___x_1573_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
lean_ctor_set(v___x_1573_, 2, v___x_1570_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat__(void){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat___00__closed__2, &l_Lean_Parser_Tactic_mcasesPat___00__closed__2_once, _init_l_Lean_Parser_Tactic_mcasesPat___00__closed__2);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1649_ = l_Lean_binderIdent;
v___x_1650_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__3));
v___x_1651_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_1652_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v___x_1650_);
lean_ctor_set(v___x_1652_, 2, v___x_1649_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__6));
v___x_1657_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__4);
v___x_1658_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_1659_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v___x_1657_);
lean_ctor_set(v___x_1659_, 2, v___x_1656_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__7);
v___x_1661_ = lean_unsigned_to_nat(1024u);
v___x_1662_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
v___x_1663_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
lean_ctor_set(v___x_1663_, 1, v___x_1661_);
lean_ctor_set(v___x_1663_, 2, v___x_1660_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8, &l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8_once, _init_l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__8);
return v___x_1664_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1674_ = l_Lean_binderIdent;
v___x_1675_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__3));
v___x_1676_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_1677_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
lean_ctor_set(v___x_1677_, 2, v___x_1674_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1678_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4);
v___x_1679_ = lean_unsigned_to_nat(1022u);
v___x_1680_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
v___x_1681_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v___x_1679_);
lean_ctor_set(v___x_1681_, 2, v___x_1678_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_u25a1__(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__5);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1692_ = l_Lean_binderIdent;
v___x_1693_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__3));
v___x_1694_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_1695_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v___x_1692_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1696_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__4);
v___x_1697_ = lean_unsigned_to_nat(1022u);
v___x_1698_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1));
v___x_1699_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1699_, 0, v___x_1698_);
lean_ctor_set(v___x_1699_, 1, v___x_1697_);
lean_ctor_set(v___x_1699_, 2, v___x_1696_);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x25__(void){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__5);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1(lean_object* v_x_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1704_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x25___00__closed__1));
lean_inc(v_x_1701_);
v___x_1705_ = l_Lean_Syntax_isOfKind(v_x_1701_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_dec(v_x_1701_);
v___x_1706_ = lean_box(1);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v_a_1703_);
return v___x_1707_;
}
else
{
lean_object* v_ref_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_ref_1708_ = lean_ctor_get(v_a_1702_, 5);
v___x_1709_ = lean_unsigned_to_nat(1u);
v___x_1710_ = l_Lean_Syntax_getArg(v_x_1701_, v___x_1709_);
lean_dec(v_x_1701_);
v___x_1711_ = 0;
v___x_1712_ = l_Lean_SourceInfo_fromRef(v_ref_1708_, v___x_1711_);
v___x_1713_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
v___x_1714_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2));
lean_inc_n(v___x_1712_, 2);
v___x_1715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1712_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5));
v___x_1717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1712_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_Syntax_node3(v___x_1712_, v___x_1713_, v___x_1715_, v___x_1710_, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v_a_1703_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1___boxed(lean_object* v_x_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x25____1(v_x_1720_, v_a_1721_, v_a_1722_);
lean_dec_ref(v_a_1721_);
return v_res_1723_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4(void){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_binderIdent;
v___x_1734_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__3));
v___x_1735_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_1736_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___x_1734_);
lean_ctor_set(v___x_1736_, 2, v___x_1733_);
return v___x_1736_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4);
v___x_1738_ = lean_unsigned_to_nat(1022u);
v___x_1739_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1));
v___x_1740_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1738_);
lean_ctor_set(v___x_1740_, 2, v___x_1737_);
return v___x_1740_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mcasesPat_x23__(void){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__5);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1(lean_object* v_x_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__1));
lean_inc(v_x_1742_);
v___x_1746_ = l_Lean_Syntax_isOfKind(v_x_1742_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_x_1742_);
v___x_1747_ = lean_box(1);
v___x_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_a_1744_);
return v___x_1748_;
}
else
{
lean_object* v_ref_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_ref_1749_ = lean_ctor_get(v_a_1743_, 5);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = l_Lean_Syntax_getArg(v_x_1742_, v___x_1750_);
lean_dec(v_x_1742_);
v___x_1752_ = 0;
v___x_1753_ = l_Lean_SourceInfo_fromRef(v_ref_1749_, v___x_1752_);
v___x_1754_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
v___x_1755_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2));
lean_inc(v___x_1753_);
v___x_1756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1753_);
lean_ctor_set(v___x_1756_, 1, v___x_1755_);
v___x_1757_ = l_Lean_Syntax_node2(v___x_1753_, v___x_1754_, v___x_1756_, v___x_1751_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_a_1744_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1___boxed(lean_object* v_x_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesPat_x23____1(v_x_1759_, v_a_1760_, v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx(lean_object* v_x_1763_){
_start:
{
switch(lean_obj_tag(v_x_1763_))
{
case 0:
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
return v___x_1764_;
}
case 1:
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_unsigned_to_nat(1u);
return v___x_1765_;
}
case 2:
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_unsigned_to_nat(2u);
return v___x_1766_;
}
case 3:
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(3u);
return v___x_1767_;
}
case 4:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_unsigned_to_nat(4u);
return v___x_1768_;
}
default: 
{
lean_object* v___x_1769_; 
v___x_1769_ = lean_unsigned_to_nat(5u);
return v___x_1769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorIdx___boxed(lean_object* v_x_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Parser_Tactic_MCasesPat_ctorIdx(v_x_1770_);
lean_dec(v_x_1770_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(lean_object* v_t_1772_, lean_object* v_k_1773_){
_start:
{
if (lean_obj_tag(v_t_1772_) == 1)
{
return v_k_1773_;
}
else
{
lean_object* v_name_1774_; lean_object* v___x_1775_; 
v_name_1774_ = lean_ctor_get(v_t_1772_, 0);
lean_inc(v_name_1774_);
lean_dec(v_t_1772_);
v___x_1775_ = lean_apply_1(v_k_1773_, v_name_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim(lean_object* v_motive__1_1776_, lean_object* v_ctorIdx_1777_, lean_object* v_t_1778_, lean_object* v_h_1779_, lean_object* v_k_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1778_, v_k_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_ctorElim___boxed(lean_object* v_motive__1_1782_, lean_object* v_ctorIdx_1783_, lean_object* v_t_1784_, lean_object* v_h_1785_, lean_object* v_k_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim(v_motive__1_1782_, v_ctorIdx_1783_, v_t_1784_, v_h_1785_, v_k_1786_);
lean_dec(v_ctorIdx_1783_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim___redArg(lean_object* v_t_1788_, lean_object* v_one_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1788_, v_one_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_one_elim(lean_object* v_motive__1_1791_, lean_object* v_t_1792_, lean_object* v_h_1793_, lean_object* v_one_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1792_, v_one_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim___redArg(lean_object* v_t_1796_, lean_object* v_clear_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1796_, v_clear_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_clear_elim(lean_object* v_motive__1_1799_, lean_object* v_t_1800_, lean_object* v_h_1801_, lean_object* v_clear_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1800_, v_clear_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim___redArg(lean_object* v_t_1804_, lean_object* v_tuple_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1804_, v_tuple_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_tuple_elim(lean_object* v_motive__1_1807_, lean_object* v_t_1808_, lean_object* v_h_1809_, lean_object* v_tuple_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1808_, v_tuple_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim___redArg(lean_object* v_t_1812_, lean_object* v_alts_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1812_, v_alts_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_alts_elim(lean_object* v_motive__1_1815_, lean_object* v_t_1816_, lean_object* v_h_1817_, lean_object* v_alts_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1816_, v_alts_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim___redArg(lean_object* v_t_1820_, lean_object* v_pure_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1820_, v_pure_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_pure_elim(lean_object* v_motive__1_1823_, lean_object* v_t_1824_, lean_object* v_h_1825_, lean_object* v_pure_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1824_, v_pure_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim___redArg(lean_object* v_t_1828_, lean_object* v_stateful_1829_){
_start:
{
lean_object* v___x_1830_; 
v___x_1830_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1828_, v_stateful_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_stateful_elim(lean_object* v_motive__1_1831_, lean_object* v_t_1832_, lean_object* v_h_1833_, lean_object* v_stateful_1834_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lean_Parser_Tactic_MCasesPat_ctorElim___redArg(v_t_1832_, v_stateful_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = lean_unsigned_to_nat(2u);
v___x_1846_ = lean_nat_to_int(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = lean_nat_to_int(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_x_1865_){
_start:
{
if (lean_obj_tag(v_x_1865_) == 0)
{
lean_dec(v_x_1863_);
return v_x_1864_;
}
else
{
lean_object* v_head_1866_; lean_object* v_tail_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1878_; 
v_head_1866_ = lean_ctor_get(v_x_1865_, 0);
v_tail_1867_ = lean_ctor_get(v_x_1865_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_x_1865_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1869_ = v_x_1865_;
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_tail_1867_);
lean_inc(v_head_1866_);
lean_dec(v_x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1878_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
lean_inc(v_x_1863_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set_tag(v___x_1869_, 5);
lean_ctor_set(v___x_1869_, 1, v_x_1863_);
lean_ctor_set(v___x_1869_, 0, v_x_1864_);
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_x_1864_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_x_1863_);
v___x_1872_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_head_1866_, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1872_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v_x_1864_ = v___x_1875_;
v_x_1865_ = v_tail_1867_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1(lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
if (lean_obj_tag(v_x_1881_) == 0)
{
lean_dec(v_x_1879_);
return v_x_1880_;
}
else
{
lean_object* v_head_1882_; lean_object* v_tail_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1894_; 
v_head_1882_ = lean_ctor_get(v_x_1881_, 0);
v_tail_1883_ = lean_ctor_get(v_x_1881_, 1);
v_isSharedCheck_1894_ = !lean_is_exclusive(v_x_1881_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1885_ = v_x_1881_;
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_tail_1883_);
lean_inc(v_head_1882_);
lean_dec(v_x_1881_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
lean_inc(v_x_1879_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set_tag(v___x_1885_, 5);
lean_ctor_set(v___x_1885_, 1, v_x_1879_);
lean_ctor_set(v___x_1885_, 0, v_x_1880_);
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_x_1880_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_x_1879_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_head_1882_, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1_spec__3(v_x_1879_, v___x_1891_, v_tail_1883_);
return v___x_1892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0(lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
if (lean_obj_tag(v_x_1895_) == 0)
{
lean_object* v___x_1897_; 
lean_dec(v_x_1896_);
v___x_1897_ = lean_box(0);
return v___x_1897_;
}
else
{
lean_object* v_tail_1898_; 
v_tail_1898_ = lean_ctor_get(v_x_1895_, 1);
if (lean_obj_tag(v_tail_1898_) == 0)
{
lean_object* v_head_1899_; lean_object* v___x_1900_; 
lean_dec(v_x_1896_);
v_head_1899_ = lean_ctor_get(v_x_1895_, 0);
lean_inc(v_head_1899_);
lean_dec_ref(v_x_1895_);
v___x_1900_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(v_head_1899_);
return v___x_1900_;
}
else
{
lean_object* v_head_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc(v_tail_1898_);
v_head_1901_ = lean_ctor_get(v_x_1895_, 0);
lean_inc(v_head_1901_);
lean_dec_ref(v_x_1895_);
v___x_1902_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(v_head_1901_);
v___x_1903_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0_spec__1(v_x_1896_, v___x_1902_, v_tail_1898_);
return v___x_1903_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_1905_ = lean_string_length(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__4);
v___x_1907_ = lean_nat_to_int(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(lean_object* v_a_1912_){
_start:
{
if (lean_obj_tag(v_a_1912_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1));
return v___x_1913_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1914_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3));
v___x_1915_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0(v_a_1912_, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5);
v___x_1917_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6));
v___x_1918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v___x_1915_);
v___x_1919_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7));
v___x_1920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = 0;
v___x_1923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set_uint8(v___x_1923_, sizeof(void*)*1, v___x_1922_);
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr(lean_object* v_x_1942_, lean_object* v_prec_1943_){
_start:
{
lean_object* v___y_1945_; 
switch(lean_obj_tag(v_x_1942_))
{
case 0:
{
lean_object* v_name_1951_; lean_object* v___y_1953_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_name_1951_ = lean_ctor_get(v_x_1942_, 0);
lean_inc(v_name_1951_);
lean_dec_ref(v_x_1942_);
v___x_1961_ = lean_unsigned_to_nat(1024u);
v___x_1962_ = lean_nat_dec_le(v___x_1961_, v_prec_1943_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1953_ = v___x_1963_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1953_ = v___x_1964_;
goto v___jp_1952_;
}
v___jp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1954_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__4));
v___x_1955_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_1951_);
v___x_1956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
lean_inc(v___y_1953_);
v___x_1957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___y_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = 0;
v___x_1959_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*1, v___x_1958_);
v___x_1960_ = l_Repr_addAppParen(v___x_1959_, v_prec_1943_);
return v___x_1960_;
}
}
case 1:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = lean_unsigned_to_nat(1024u);
v___x_1966_ = lean_nat_dec_le(v___x_1965_, v_prec_1943_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1945_ = v___x_1967_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1968_; 
v___x_1968_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1945_ = v___x_1968_;
goto v___jp_1944_;
}
}
case 2:
{
lean_object* v_args_1969_; lean_object* v___y_1971_; lean_object* v___x_1979_; uint8_t v___x_1980_; 
v_args_1969_ = lean_ctor_get(v_x_1942_, 0);
lean_inc(v_args_1969_);
lean_dec_ref(v_x_1942_);
v___x_1979_ = lean_unsigned_to_nat(1024u);
v___x_1980_ = lean_nat_dec_le(v___x_1979_, v_prec_1943_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1971_ = v___x_1981_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1982_; 
v___x_1982_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1971_ = v___x_1982_;
goto v___jp_1970_;
}
v___jp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1972_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__9));
v___x_1973_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_args_1969_);
v___x_1974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
lean_inc(v___y_1971_);
v___x_1975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___y_1971_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = 0;
v___x_1977_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*1, v___x_1976_);
v___x_1978_ = l_Repr_addAppParen(v___x_1977_, v_prec_1943_);
return v___x_1978_;
}
}
case 3:
{
lean_object* v_args_1983_; lean_object* v___y_1985_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_args_1983_ = lean_ctor_get(v_x_1942_, 0);
lean_inc(v_args_1983_);
lean_dec_ref(v_x_1942_);
v___x_1993_ = lean_unsigned_to_nat(1024u);
v___x_1994_ = lean_nat_dec_le(v___x_1993_, v_prec_1943_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1985_ = v___x_1995_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1996_; 
v___x_1996_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1985_ = v___x_1996_;
goto v___jp_1984_;
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1986_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__12));
v___x_1987_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_args_1983_);
v___x_1988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
lean_inc(v___y_1985_);
v___x_1989_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___y_1985_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = 0;
v___x_1991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set_uint8(v___x_1991_, sizeof(void*)*1, v___x_1990_);
v___x_1992_ = l_Repr_addAppParen(v___x_1991_, v_prec_1943_);
return v___x_1992_;
}
}
case 4:
{
lean_object* v_h_1997_; lean_object* v___y_1999_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_h_1997_ = lean_ctor_get(v_x_1942_, 0);
lean_inc(v_h_1997_);
lean_dec_ref(v_x_1942_);
v___x_2007_ = lean_unsigned_to_nat(1024u);
v___x_2008_ = lean_nat_dec_le(v___x_2007_, v_prec_1943_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_1999_ = v___x_2009_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2010_; 
v___x_2010_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_1999_ = v___x_2010_;
goto v___jp_1998_;
}
v___jp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_2000_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__15));
v___x_2001_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_1997_);
v___x_2002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
lean_inc(v___y_1999_);
v___x_2003_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___y_1999_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = 0;
v___x_2005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*1, v___x_2004_);
v___x_2006_ = l_Repr_addAppParen(v___x_2005_, v_prec_1943_);
return v___x_2006_;
}
}
default: 
{
lean_object* v_h_2011_; lean_object* v___y_2013_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_h_2011_ = lean_ctor_get(v_x_1942_, 0);
lean_inc(v_h_2011_);
lean_dec_ref(v_x_1942_);
v___x_2021_ = lean_unsigned_to_nat(1024u);
v___x_2022_ = lean_nat_dec_le(v___x_2021_, v_prec_1943_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2013_ = v___x_2023_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2013_ = v___x_2024_;
goto v___jp_2012_;
}
v___jp_2012_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2014_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__18));
v___x_2015_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2011_);
v___x_2016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2014_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
lean_inc(v___y_2013_);
v___x_2017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2013_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = 0;
v___x_2019_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*1, v___x_2018_);
v___x_2020_ = l_Repr_addAppParen(v___x_2019_, v_prec_1943_);
return v___x_2020_;
}
}
}
v___jp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1946_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__1));
lean_inc(v___y_1945_);
v___x_1947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___y_1945_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = 0;
v___x_1949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*1, v___x_1948_);
v___x_1950_ = l_Repr_addAppParen(v___x_1949_, v_prec_1943_);
return v___x_1950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(lean_object* v___y_2025_){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v___y_2025_, v___x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMCasesPat_repr___boxed(lean_object* v_x_2028_, lean_object* v_prec_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_Parser_Tactic_instReprMCasesPat_repr(v_x_2028_, v_prec_2029_);
lean_dec(v_prec_2029_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__1(lean_object* v_a_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_nat_to_int(v_a_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0(lean_object* v_a_2033_, lean_object* v_n_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg(v_a_2033_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___boxed(lean_object* v_a_2036_, lean_object* v_n_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0(v_a_2036_, v_n_2037_);
lean_dec(v_n_2037_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(uint8_t v___x_2045_, uint8_t v___x_2046_, lean_object* v_as_2047_, size_t v_i_2048_, size_t v_stop_2049_, lean_object* v_b_2050_){
_start:
{
lean_object* v___y_2052_; uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_eq(v_i_2048_, v_stop_2049_);
if (v___x_2056_ == 0)
{
lean_object* v_fst_2057_; uint8_t v___x_2058_; 
v_fst_2057_ = lean_ctor_get(v_b_2050_, 0);
v___x_2058_ = lean_unbox(v_fst_2057_);
if (v___x_2058_ == 0)
{
lean_object* v_snd_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2067_; 
v_snd_2059_ = lean_ctor_get(v_b_2050_, 1);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_b_2050_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v_b_2050_, 0);
lean_dec(v_unused_2068_);
v___x_2061_ = v_b_2050_;
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_snd_2059_);
lean_dec(v_b_2050_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_box(v___x_2045_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2063_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_snd_2059_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v___y_2052_ = v___x_2065_;
goto v___jp_2051_;
}
}
}
else
{
lean_object* v_snd_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2079_; 
v_snd_2069_ = lean_ctor_get(v_b_2050_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_b_2050_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v_b_2050_, 0);
lean_dec(v_unused_2080_);
v___x_2071_ = v_b_2050_;
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_snd_2069_);
lean_dec(v_b_2050_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2079_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2073_ = lean_array_uget_borrowed(v_as_2047_, v_i_2048_);
lean_inc(v___x_2073_);
v___x_2074_ = lean_array_push(v_snd_2069_, v___x_2073_);
v___x_2075_ = lean_box(v___x_2046_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2074_);
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2077_ = v___x_2071_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v___x_2074_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
v___y_2052_ = v___x_2077_;
goto v___jp_2051_;
}
}
}
}
else
{
return v_b_2050_;
}
v___jp_2051_:
{
size_t v___x_2053_; size_t v___x_2054_; 
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2048_, v___x_2053_);
v_i_2048_ = v___x_2054_;
v_b_2050_ = v___y_2052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2___boxed(lean_object* v___x_2081_, lean_object* v___x_2082_, lean_object* v_as_2083_, lean_object* v_i_2084_, lean_object* v_stop_2085_, lean_object* v_b_2086_){
_start:
{
uint8_t v___x_1958__boxed_2087_; uint8_t v___x_1959__boxed_2088_; size_t v_i_boxed_2089_; size_t v_stop_boxed_2090_; lean_object* v_res_2091_; 
v___x_1958__boxed_2087_ = lean_unbox(v___x_2081_);
v___x_1959__boxed_2088_ = lean_unbox(v___x_2082_);
v_i_boxed_2089_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_stop_boxed_2090_ = lean_unbox_usize(v_stop_2085_);
lean_dec(v_stop_2085_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_1958__boxed_2087_, v___x_1959__boxed_2088_, v_as_2083_, v_i_boxed_2089_, v_stop_boxed_2090_, v_b_2086_);
lean_dec_ref(v_as_2083_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_bs_2094_){
_start:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v_bs_2094_);
return v___x_2096_;
}
else
{
lean_object* v_v_2097_; lean_object* v___x_2098_; lean_object* v_bs_x27_2099_; size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v_v_2097_ = lean_array_uget(v_bs_2094_, v_i_2093_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v_bs_x27_2099_ = lean_array_uset(v_bs_2094_, v_i_2093_, v___x_2098_);
v___x_2100_ = ((size_t)1ULL);
v___x_2101_ = lean_usize_add(v_i_2093_, v___x_2100_);
v___x_2102_ = lean_array_uset(v_bs_x27_2099_, v_i_2093_, v_v_2097_);
v_i_2093_ = v___x_2101_;
v_bs_2094_ = v___x_2102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0___boxed(lean_object* v_sz_2104_, lean_object* v_i_2105_, lean_object* v_bs_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2104_);
lean_dec(v_sz_2104_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2105_);
lean_dec(v_i_2105_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(v_sz_boxed_2107_, v_i_boxed_2108_, v_bs_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_go(lean_object* v_a_2118_){
_start:
{
lean_object* v___y_2120_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
lean_inc(v_a_2118_);
v___x_2146_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x2d___closed__1));
lean_inc(v_a_2118_);
v___x_2148_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u27e8___u27e9___closed__1));
lean_inc(v_a_2118_);
v___x_2150_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; uint8_t v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__1));
lean_inc(v_a_2118_);
v___x_2152_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2151_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__1));
lean_inc(v_a_2118_);
v___x_2154_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_x28___x29___closed__1));
lean_inc(v_a_2118_);
v___x_2156_ = l_Lean_Syntax_isOfKind(v_a_2118_, v___x_2155_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_a_2118_);
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
else
{
lean_object* v___x_2158_; lean_object* v_pat_2159_; lean_object* v___x_2160_; 
v___x_2158_ = lean_unsigned_to_nat(1u);
v_pat_2159_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2158_);
lean_dec(v_a_2118_);
v___x_2160_ = l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(v_pat_2159_);
return v___x_2160_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v_h_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2161_ = lean_unsigned_to_nat(1u);
v_h_2162_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2161_);
lean_dec(v_a_2118_);
v___x_2163_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_h_2162_);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
else
{
lean_object* v___x_2165_; lean_object* v_h_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v_h_2166_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2165_);
lean_dec(v_a_2118_);
v___x_2167_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2167_, 0, v_h_2166_);
v___x_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2169_ = lean_unsigned_to_nat(1u);
v___x_2170_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2169_);
lean_dec(v_a_2118_);
v___x_2171_ = l_Lean_Syntax_getArgs(v___x_2170_);
lean_dec(v___x_2170_);
v___x_2172_ = lean_unsigned_to_nat(0u);
v___x_2173_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___x_2174_ = lean_array_get_size(v___x_2171_);
v___x_2175_ = lean_nat_dec_lt(v___x_2172_, v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2171_);
v___y_2120_ = v___x_2173_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = lean_box(v___x_2150_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2173_);
v___x_2178_ = lean_nat_dec_le(v___x_2174_, v___x_2174_);
if (v___x_2178_ == 0)
{
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2177_);
lean_dec_ref(v___x_2171_);
v___y_2120_ = v___x_2173_;
goto v___jp_2119_;
}
else
{
size_t v___x_2179_; size_t v___x_2180_; lean_object* v___x_2181_; lean_object* v_snd_2182_; 
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = lean_usize_of_nat(v___x_2174_);
v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2150_, v___x_2148_, v___x_2171_, v___x_2179_, v___x_2180_, v___x_2177_);
lean_dec_ref(v___x_2171_);
v_snd_2182_ = lean_ctor_get(v___x_2181_, 1);
lean_inc(v_snd_2182_);
lean_dec_ref(v___x_2181_);
v___y_2120_ = v_snd_2182_;
goto v___jp_2119_;
}
}
else
{
size_t v___x_2183_; size_t v___x_2184_; lean_object* v___x_2185_; lean_object* v_snd_2186_; 
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = lean_usize_of_nat(v___x_2174_);
v___x_2185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2150_, v___x_2148_, v___x_2171_, v___x_2183_, v___x_2184_, v___x_2177_);
lean_dec_ref(v___x_2171_);
v_snd_2186_ = lean_ctor_get(v___x_2185_, 1);
lean_inc(v_snd_2186_);
lean_dec_ref(v___x_2185_);
v___y_2120_ = v_snd_2186_;
goto v___jp_2119_;
}
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec(v_a_2118_);
v___x_2187_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1));
return v___x_2187_;
}
}
else
{
lean_object* v___x_2188_; lean_object* v_name_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2188_ = lean_unsigned_to_nat(0u);
v_name_2189_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2188_);
lean_dec(v_a_2118_);
v___x_2190_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2189_);
v___x_2191_ = l_Lean_Syntax_isOfKind(v_name_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; 
lean_dec(v_name_2189_);
v___x_2192_ = lean_box(0);
return v___x_2192_;
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_name_2189_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
v___jp_2119_:
{
size_t v_sz_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v_sz_2121_ = lean_array_size(v___y_2120_);
v___x_2122_ = ((size_t)0ULL);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__0(v_sz_2121_, v___x_2122_, v___y_2120_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_box(0);
return v___x_2124_;
}
else
{
lean_object* v_val_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2144_; 
v_val_2125_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2127_ = v___x_2123_;
v_isShared_2128_ = v_isSharedCheck_2144_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_val_2125_);
lean_dec(v___x_2123_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2144_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
size_t v_sz_2129_; lean_object* v___x_2130_; 
v_sz_2129_ = lean_array_size(v_val_2125_);
v___x_2130_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(v_sz_2129_, v___x_2122_, v_val_2125_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
lean_del_object(v___x_2127_);
v___x_2131_ = lean_box(0);
return v___x_2131_;
}
else
{
lean_object* v_val_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2143_; 
v_val_2132_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2134_ = v___x_2130_;
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_val_2132_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2143_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2136_ = lean_array_to_list(v_val_2132_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set_tag(v___x_2127_, 2);
lean_ctor_set(v___x_2127_, 0, v___x_2136_);
v___x_2138_ = v___x_2127_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2135_ == 0)
{
lean_ctor_set(v___x_2134_, 0, v___x_2138_);
v___x_2140_ = v___x_2134_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(size_t v_sz_2195_, size_t v_i_2196_, lean_object* v_bs_2197_){
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
v___x_2201_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_v_2200_);
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
lean_dec_ref(v___x_2201_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(lean_object* v_a_2210_){
_start:
{
lean_object* v___x_2211_; uint8_t v___x_2212_; 
v___x_2211_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__1));
lean_inc(v_a_2210_);
v___x_2212_ = l_Lean_Syntax_isOfKind(v_a_2210_, v___x_2211_);
if (v___x_2212_ == 0)
{
lean_object* v___x_2213_; 
lean_dec(v_a_2210_);
v___x_2213_ = lean_box(0);
return v___x_2213_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_args_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = l_Lean_Syntax_getArg(v_a_2210_, v___x_2214_);
lean_dec(v_a_2210_);
v_args_2216_ = l_Lean_Syntax_getArgs(v___x_2215_);
lean_dec(v___x_2215_);
v___x_2217_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2216_);
lean_dec_ref(v_args_2216_);
v___x_2218_ = lean_array_get_size(v___x_2217_);
v___x_2219_ = lean_unsigned_to_nat(1u);
v___x_2220_ = lean_nat_dec_eq(v___x_2218_, v___x_2219_);
if (v___x_2220_ == 0)
{
size_t v_sz_2221_; size_t v___x_2222_; lean_object* v___x_2223_; 
v_sz_2221_ = lean_array_size(v___x_2217_);
v___x_2222_ = ((size_t)0ULL);
v___x_2223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_2221_, v___x_2222_, v___x_2217_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_val_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2234_; 
v_val_2225_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2227_ = v___x_2223_;
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_val_2225_);
lean_dec(v___x_2223_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = lean_array_to_list(v_val_2225_);
v___x_2230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2230_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_array_fget(v___x_2217_, v___x_2214_);
lean_dec_ref(v___x_2217_);
v___x_2236_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v___x_2235_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(size_t v_sz_2237_, size_t v_i_2238_, lean_object* v_bs_2239_){
_start:
{
uint8_t v___x_2240_; 
v___x_2240_ = lean_usize_dec_lt(v_i_2238_, v_sz_2237_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; 
v___x_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2241_, 0, v_bs_2239_);
return v___x_2241_;
}
else
{
lean_object* v_v_2242_; lean_object* v___x_2243_; 
v_v_2242_ = lean_array_uget_borrowed(v_bs_2239_, v_i_2238_);
lean_inc(v_v_2242_);
v___x_2243_ = l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(v_v_2242_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v___x_2244_; 
lean_dec_ref(v_bs_2239_);
v___x_2244_ = lean_box(0);
return v___x_2244_;
}
else
{
lean_object* v_val_2245_; lean_object* v___x_2246_; lean_object* v_bs_x27_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v_val_2245_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_val_2245_);
lean_dec_ref(v___x_2243_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v_bs_x27_2247_ = lean_array_uset(v_bs_2239_, v_i_2238_, v___x_2246_);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_add(v_i_2238_, v___x_2248_);
v___x_2250_ = lean_array_uset(v_bs_x27_2247_, v_i_2238_, v_val_2245_);
v_i_2238_ = v___x_2249_;
v_bs_2239_ = v___x_2250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1___boxed(lean_object* v_sz_2252_, lean_object* v_i_2253_, lean_object* v_bs_2254_){
_start:
{
size_t v_sz_boxed_2255_; size_t v_i_boxed_2256_; lean_object* v_res_2257_; 
v_sz_boxed_2255_ = lean_unbox_usize(v_sz_2252_);
lean_dec(v_sz_2252_);
v_i_boxed_2256_ = lean_unbox_usize(v_i_2253_);
lean_dec(v_i_2253_);
v_res_2257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(v_sz_boxed_2255_, v_i_boxed_2256_, v_bs_2254_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4___boxed(lean_object* v_sz_2258_, lean_object* v_i_2259_, lean_object* v_bs_2260_){
_start:
{
size_t v_sz_boxed_2261_; size_t v_i_boxed_2262_; lean_object* v_res_2263_; 
v_sz_boxed_2261_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2262_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_boxed_2261_, v_i_boxed_2262_, v_bs_2260_);
return v_res_2263_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(lean_object* v_k_2270_){
_start:
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1));
v___x_2272_ = lean_name_eq(v_k_2270_, v___x_2271_);
if (v___x_2272_ == 0)
{
uint8_t v___x_2273_; 
v___x_2273_ = 1;
return v___x_2273_;
}
else
{
uint8_t v___x_2274_; 
v___x_2274_ = 0;
return v___x_2274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___boxed(lean_object* v_k_2275_){
_start:
{
uint8_t v_res_2276_; lean_object* v_r_2277_; 
v_res_2276_ = l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(v_k_2275_);
lean_dec(v_k_2275_);
v_r_2277_ = lean_box(v_res_2276_);
return v_r_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse(lean_object* v_pat_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; 
v___f_2282_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2280_);
v___x_2283_ = l_Lean_expandMacros(v_pat_2279_, v___f_2282_, v_a_2280_, v_a_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2295_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_a_2285_ = lean_ctor_get(v___x_2283_, 1);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2295_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2295_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_a_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
lean_del_object(v___x_2287_);
v___x_2290_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2285_);
return v___x_2290_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; 
v_val_2291_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_val_2291_);
lean_dec_ref(v___x_2289_);
if (v_isShared_2288_ == 0)
{
lean_ctor_set(v___x_2287_, 0, v_val_2291_);
v___x_2293_ = v___x_2287_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_val_2291_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_a_2285_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2283_, 0);
v_a_2297_ = lean_ctor_get(v___x_2283_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2283_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
lean_dec(v___x_2283_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2296_);
lean_ctor_set(v_reuseFailAlloc_2303_, 1, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object* v_pat_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Parser_Tactic_MCasesPat_parse(v_pat_2305_, v_a_2306_, v_a_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(lean_object* v_x_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesError___closed__1));
v___x_2354_ = l_Lean_Syntax_isOfKind(v_x_2350_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_box(1);
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_a_2352_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0));
v___x_2358_ = l_Lean_Macro_throwError___redArg(v___x_2357_, v_a_2351_, v_a_2352_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_a_2360_ = lean_ctor_get(v___x_2358_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2358_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2359_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2368_ = lean_ctor_get(v___x_2358_, 0);
v_a_2369_ = lean_ctor_get(v___x_2358_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2358_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_inc(v_a_2368_);
lean_dec(v___x_2358_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2368_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___boxed(lean_object* v_x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(v_x_2377_, v_a_2378_, v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2380_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrefinePat(void){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_box(0);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2(void){
_start:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = l_Lean_binderIdent;
v___x_2418_ = lean_unsigned_to_nat(1022u);
v___x_2419_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
v___x_2420_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set(v___x_2420_, 2, v___x_2417_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat__(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2);
return v___x_2421_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2501_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4);
v___x_2502_ = lean_unsigned_to_nat(1022u);
v___x_2503_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2504_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
lean_ctor_set(v___x_2504_, 1, v___x_2502_);
lean_ctor_set(v___x_2504_, 2, v___x_2501_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1__(void){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2);
return v___x_2505_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2515_ = l_Lean_binderIdent;
v___x_2516_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3));
v___x_2517_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_2518_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2516_);
lean_ctor_set(v___x_2518_, 2, v___x_2515_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2519_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4);
v___x_2520_ = lean_unsigned_to_nat(1022u);
v___x_2521_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
v___x_2522_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2520_);
lean_ctor_set(v___x_2522_, 2, v___x_2519_);
return v___x_2522_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f__(void){
_start:
{
lean_object* v___x_2523_; 
v___x_2523_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(lean_object* v_x_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1));
lean_inc(v_x_2539_);
v___x_2543_ = l_Lean_Syntax_isOfKind(v_x_2539_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec(v_x_2539_);
v___x_2544_ = lean_box(1);
v___x_2545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
lean_ctor_set(v___x_2545_, 1, v_a_2541_);
return v___x_2545_;
}
else
{
lean_object* v_ref_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_ref_2546_ = lean_ctor_get(v_a_2540_, 5);
v___x_2547_ = lean_unsigned_to_nat(1u);
v___x_2548_ = l_Lean_Syntax_getArg(v_x_2539_, v___x_2547_);
lean_dec(v_x_2539_);
v___x_2549_ = 0;
v___x_2550_ = l_Lean_SourceInfo_fromRef(v_ref_2546_, v___x_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
v___x_2552_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2));
lean_inc_n(v___x_2550_, 2);
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2550_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5));
v___x_2555_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2550_);
lean_ctor_set(v___x_2555_, 1, v___x_2554_);
v___x_2556_ = l_Lean_Syntax_node3(v___x_2550_, v___x_2551_, v___x_2553_, v___x_2548_, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v_a_2541_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1___boxed(lean_object* v_x_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(v_x_2558_, v_a_2559_, v_a_2560_);
lean_dec_ref(v_a_2559_);
return v_res_2561_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2568_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4);
v___x_2569_ = lean_unsigned_to_nat(1022u);
v___x_2570_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
v___x_2571_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v___x_2569_);
lean_ctor_set(v___x_2571_, 2, v___x_2568_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23__(void){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(lean_object* v_x_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
lean_inc(v_x_2573_);
v___x_2577_ = l_Lean_Syntax_isOfKind(v_x_2573_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v_x_2573_);
v___x_2578_ = lean_box(1);
v___x_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v_a_2575_);
return v___x_2579_;
}
else
{
lean_object* v_ref_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_ref_2580_ = lean_ctor_get(v_a_2574_, 5);
v___x_2581_ = lean_unsigned_to_nat(1u);
v___x_2582_ = l_Lean_Syntax_getArg(v_x_2573_, v___x_2581_);
lean_dec(v_x_2573_);
v___x_2583_ = 0;
v___x_2584_ = l_Lean_SourceInfo_fromRef(v_ref_2580_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2586_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2));
lean_inc(v___x_2584_);
v___x_2587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = l_Lean_Syntax_node2(v___x_2584_, v___x_2585_, v___x_2587_, v___x_2582_);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2588_);
lean_ctor_set(v___x_2589_, 1, v_a_2575_);
return v___x_2589_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1___boxed(lean_object* v_x_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(v_x_2590_, v_a_2591_, v_a_2592_);
lean_dec_ref(v_a_2591_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx(lean_object* v_x_2594_){
_start:
{
switch(lean_obj_tag(v_x_2594_))
{
case 0:
{
lean_object* v___x_2595_; 
v___x_2595_ = lean_unsigned_to_nat(0u);
return v___x_2595_;
}
case 1:
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_unsigned_to_nat(1u);
return v___x_2596_;
}
case 2:
{
lean_object* v___x_2597_; 
v___x_2597_ = lean_unsigned_to_nat(2u);
return v___x_2597_;
}
case 3:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_unsigned_to_nat(3u);
return v___x_2598_;
}
default: 
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_unsigned_to_nat(4u);
return v___x_2599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___boxed(lean_object* v_x_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Parser_Tactic_MRefinePat_ctorIdx(v_x_2600_);
lean_dec_ref(v_x_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(lean_object* v_t_2602_, lean_object* v_k_2603_){
_start:
{
lean_object* v_name_2604_; lean_object* v___x_2605_; 
v_name_2604_ = lean_ctor_get(v_t_2602_, 0);
lean_inc(v_name_2604_);
lean_dec_ref(v_t_2602_);
v___x_2605_ = lean_apply_1(v_k_2603_, v_name_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim(lean_object* v_motive__1_2606_, lean_object* v_ctorIdx_2607_, lean_object* v_t_2608_, lean_object* v_h_2609_, lean_object* v_k_2610_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2608_, v_k_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___boxed(lean_object* v_motive__1_2612_, lean_object* v_ctorIdx_2613_, lean_object* v_t_2614_, lean_object* v_h_2615_, lean_object* v_k_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim(v_motive__1_2612_, v_ctorIdx_2613_, v_t_2614_, v_h_2615_, v_k_2616_);
lean_dec(v_ctorIdx_2613_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim___redArg(lean_object* v_t_2618_, lean_object* v_one_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2618_, v_one_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim(lean_object* v_motive__1_2621_, lean_object* v_t_2622_, lean_object* v_h_2623_, lean_object* v_one_2624_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2622_, v_one_2624_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim___redArg(lean_object* v_t_2626_, lean_object* v_tuple_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2626_, v_tuple_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim(lean_object* v_motive__1_2629_, lean_object* v_t_2630_, lean_object* v_h_2631_, lean_object* v_tuple_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2630_, v_tuple_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim___redArg(lean_object* v_t_2634_, lean_object* v_pure_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2634_, v_pure_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim(lean_object* v_motive__1_2637_, lean_object* v_t_2638_, lean_object* v_h_2639_, lean_object* v_pure_2640_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2638_, v_pure_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim___redArg(lean_object* v_t_2642_, lean_object* v_stateful_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2642_, v_stateful_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim(lean_object* v_motive__1_2645_, lean_object* v_t_2646_, lean_object* v_h_2647_, lean_object* v_stateful_2648_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2646_, v_stateful_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim___redArg(lean_object* v_t_2650_, lean_object* v_hole_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2650_, v_hole_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim(lean_object* v_motive__1_2653_, lean_object* v_t_2654_, lean_object* v_h_2655_, lean_object* v_hole_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2654_, v_hole_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2670_, lean_object* v_x_2671_, lean_object* v_x_2672_){
_start:
{
if (lean_obj_tag(v_x_2672_) == 0)
{
lean_dec(v_x_2670_);
return v_x_2671_;
}
else
{
lean_object* v_head_2673_; lean_object* v_tail_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2685_; 
v_head_2673_ = lean_ctor_get(v_x_2672_, 0);
v_tail_2674_ = lean_ctor_get(v_x_2672_, 1);
v_isSharedCheck_2685_ = !lean_is_exclusive(v_x_2672_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2676_ = v_x_2672_;
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_tail_2674_);
lean_inc(v_head_2673_);
lean_dec(v_x_2672_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2685_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
lean_inc(v_x_2670_);
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 5);
lean_ctor_set(v___x_2676_, 1, v_x_2670_);
lean_ctor_set(v___x_2676_, 0, v_x_2671_);
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_x_2671_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_x_2670_);
v___x_2679_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_unsigned_to_nat(0u);
v___x_2681_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2673_, v___x_2680_);
v___x_2682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2679_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v_x_2671_ = v___x_2682_;
v_x_2672_ = v_tail_2674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(lean_object* v_x_2686_, lean_object* v_x_2687_, lean_object* v_x_2688_){
_start:
{
if (lean_obj_tag(v_x_2688_) == 0)
{
lean_dec(v_x_2686_);
return v_x_2687_;
}
else
{
lean_object* v_head_2689_; lean_object* v_tail_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2701_; 
v_head_2689_ = lean_ctor_get(v_x_2688_, 0);
v_tail_2690_ = lean_ctor_get(v_x_2688_, 1);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_x_2688_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2692_ = v_x_2688_;
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_tail_2690_);
lean_inc(v_head_2689_);
lean_dec(v_x_2688_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2701_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
lean_inc(v_x_2686_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 5);
lean_ctor_set(v___x_2692_, 1, v_x_2686_);
lean_ctor_set(v___x_2692_, 0, v_x_2687_);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_x_2687_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_x_2686_);
v___x_2695_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2696_ = lean_unsigned_to_nat(0u);
v___x_2697_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2689_, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2695_);
lean_ctor_set(v___x_2698_, 1, v___x_2697_);
v___x_2699_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(v_x_2686_, v___x_2698_, v_tail_2690_);
return v___x_2699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(lean_object* v_x_2702_, lean_object* v_x_2703_){
_start:
{
if (lean_obj_tag(v_x_2702_) == 0)
{
lean_object* v___x_2704_; 
lean_dec(v_x_2703_);
v___x_2704_ = lean_box(0);
return v___x_2704_;
}
else
{
lean_object* v_tail_2705_; 
v_tail_2705_ = lean_ctor_get(v_x_2702_, 1);
if (lean_obj_tag(v_tail_2705_) == 0)
{
lean_object* v_head_2706_; lean_object* v___x_2707_; 
lean_dec(v_x_2703_);
v_head_2706_ = lean_ctor_get(v_x_2702_, 0);
lean_inc(v_head_2706_);
lean_dec_ref(v_x_2702_);
v___x_2707_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2706_);
return v___x_2707_;
}
else
{
lean_object* v_head_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_inc(v_tail_2705_);
v_head_2708_ = lean_ctor_get(v_x_2702_, 0);
lean_inc(v_head_2708_);
lean_dec_ref(v_x_2702_);
v___x_2709_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2708_);
v___x_2710_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(v_x_2703_, v___x_2709_, v_tail_2705_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(lean_object* v_a_2711_){
_start:
{
if (lean_obj_tag(v_a_2711_) == 0)
{
lean_object* v___x_2712_; 
v___x_2712_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1));
return v___x_2712_;
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; 
v___x_2713_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3));
v___x_2714_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(v_a_2711_, v___x_2713_);
v___x_2715_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5);
v___x_2716_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6));
v___x_2717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v___x_2714_);
v___x_2718_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7));
v___x_2719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2717_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2715_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = 0;
v___x_2722_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*1, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr(lean_object* v_x_2741_, lean_object* v_prec_2742_){
_start:
{
switch(lean_obj_tag(v_x_2741_))
{
case 0:
{
lean_object* v_name_2743_; lean_object* v___y_2745_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v_name_2743_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_name_2743_);
lean_dec_ref(v_x_2741_);
v___x_2753_ = lean_unsigned_to_nat(1024u);
v___x_2754_ = lean_nat_dec_le(v___x_2753_, v_prec_2742_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2745_ = v___x_2755_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2745_ = v___x_2756_;
goto v___jp_2744_;
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2746_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2));
v___x_2747_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2743_);
v___x_2748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
lean_inc(v___y_2745_);
v___x_2749_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___y_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = 0;
v___x_2751_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*1, v___x_2750_);
v___x_2752_ = l_Repr_addAppParen(v___x_2751_, v_prec_2742_);
return v___x_2752_;
}
}
case 1:
{
lean_object* v_args_2757_; lean_object* v___y_2759_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_args_2757_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_args_2757_);
lean_dec_ref(v_x_2741_);
v___x_2767_ = lean_unsigned_to_nat(1024u);
v___x_2768_ = lean_nat_dec_le(v___x_2767_, v_prec_2742_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2759_ = v___x_2769_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2759_ = v___x_2770_;
goto v___jp_2758_;
}
v___jp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2760_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5));
v___x_2761_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_args_2757_);
v___x_2762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
lean_inc(v___y_2759_);
v___x_2763_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___y_2759_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = 0;
v___x_2765_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set_uint8(v___x_2765_, sizeof(void*)*1, v___x_2764_);
v___x_2766_ = l_Repr_addAppParen(v___x_2765_, v_prec_2742_);
return v___x_2766_;
}
}
case 2:
{
lean_object* v_h_2771_; lean_object* v___y_2773_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v_h_2771_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_h_2771_);
lean_dec_ref(v_x_2741_);
v___x_2781_ = lean_unsigned_to_nat(1024u);
v___x_2782_ = lean_nat_dec_le(v___x_2781_, v_prec_2742_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2773_ = v___x_2783_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2773_ = v___x_2784_;
goto v___jp_2772_;
}
v___jp_2772_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2774_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8));
v___x_2775_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2771_);
v___x_2776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2776_, 0, v___x_2774_);
lean_ctor_set(v___x_2776_, 1, v___x_2775_);
lean_inc(v___y_2773_);
v___x_2777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___y_2773_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = 0;
v___x_2779_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set_uint8(v___x_2779_, sizeof(void*)*1, v___x_2778_);
v___x_2780_ = l_Repr_addAppParen(v___x_2779_, v_prec_2742_);
return v___x_2780_;
}
}
case 3:
{
lean_object* v_h_2785_; lean_object* v___y_2787_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_h_2785_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_h_2785_);
lean_dec_ref(v_x_2741_);
v___x_2795_ = lean_unsigned_to_nat(1024u);
v___x_2796_ = lean_nat_dec_le(v___x_2795_, v_prec_2742_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
v___x_2797_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2787_ = v___x_2797_;
goto v___jp_2786_;
}
else
{
lean_object* v___x_2798_; 
v___x_2798_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2787_ = v___x_2798_;
goto v___jp_2786_;
}
v___jp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11));
v___x_2789_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2785_);
v___x_2790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
lean_inc(v___y_2787_);
v___x_2791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___y_2787_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = 0;
v___x_2793_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2793_, 0, v___x_2791_);
lean_ctor_set_uint8(v___x_2793_, sizeof(void*)*1, v___x_2792_);
v___x_2794_ = l_Repr_addAppParen(v___x_2793_, v_prec_2742_);
return v___x_2794_;
}
}
default: 
{
lean_object* v_name_2799_; lean_object* v___y_2801_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_name_2799_ = lean_ctor_get(v_x_2741_, 0);
lean_inc(v_name_2799_);
lean_dec_ref(v_x_2741_);
v___x_2809_ = lean_unsigned_to_nat(1024u);
v___x_2810_ = lean_nat_dec_le(v___x_2809_, v_prec_2742_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2801_ = v___x_2811_;
goto v___jp_2800_;
}
else
{
lean_object* v___x_2812_; 
v___x_2812_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2801_ = v___x_2812_;
goto v___jp_2800_;
}
v___jp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2802_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14));
v___x_2803_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2799_);
v___x_2804_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2802_);
lean_ctor_set(v___x_2804_, 1, v___x_2803_);
lean_inc(v___y_2801_);
v___x_2805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___y_2801_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = 0;
v___x_2807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set_uint8(v___x_2807_, sizeof(void*)*1, v___x_2806_);
v___x_2808_ = l_Repr_addAppParen(v___x_2807_, v_prec_2742_);
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_unsigned_to_nat(0u);
v___x_2815_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v___y_2813_, v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___boxed(lean_object* v_x_2816_, lean_object* v_prec_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_x_2816_, v_prec_2817_);
lean_dec(v_prec_2817_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(lean_object* v_a_2819_, lean_object* v_n_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_a_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___boxed(lean_object* v_a_2822_, lean_object* v_n_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(v_a_2822_, v_n_2823_);
lean_dec(v_n_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(size_t v_sz_2831_, size_t v_i_2832_, lean_object* v_bs_2833_){
_start:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_usize_dec_lt(v_i_2832_, v_sz_2831_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_bs_2833_);
return v___x_2835_;
}
else
{
lean_object* v_v_2836_; lean_object* v___x_2837_; lean_object* v_bs_x27_2838_; size_t v___x_2839_; size_t v___x_2840_; lean_object* v___x_2841_; 
v_v_2836_ = lean_array_uget(v_bs_2833_, v_i_2832_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v_bs_x27_2838_ = lean_array_uset(v_bs_2833_, v_i_2832_, v___x_2837_);
v___x_2839_ = ((size_t)1ULL);
v___x_2840_ = lean_usize_add(v_i_2832_, v___x_2839_);
v___x_2841_ = lean_array_uset(v_bs_x27_2838_, v_i_2832_, v_v_2836_);
v_i_2832_ = v___x_2840_;
v_bs_2833_ = v___x_2841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0___boxed(lean_object* v_sz_2843_, lean_object* v_i_2844_, lean_object* v_bs_2845_){
_start:
{
size_t v_sz_boxed_2846_; size_t v_i_boxed_2847_; lean_object* v_res_2848_; 
v_sz_boxed_2846_ = lean_unbox_usize(v_sz_2843_);
lean_dec(v_sz_2843_);
v_i_boxed_2847_ = lean_unbox_usize(v_i_2844_);
lean_dec(v_i_2844_);
v_res_2848_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_boxed_2846_, v_i_boxed_2847_, v_bs_2845_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse_go(lean_object* v_a_2849_){
_start:
{
lean_object* v___y_2851_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
lean_inc(v_a_2849_);
v___x_2877_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
lean_inc(v_a_2849_);
v___x_2879_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2878_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; uint8_t v___x_2881_; 
v___x_2880_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1));
lean_inc(v_a_2849_);
v___x_2881_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2880_);
if (v___x_2881_ == 0)
{
lean_object* v___x_2882_; uint8_t v___x_2883_; 
v___x_2882_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
lean_inc(v_a_2849_);
v___x_2883_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2882_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2884_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
lean_inc(v_a_2849_);
v___x_2885_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1));
lean_inc(v_a_2849_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v_a_2849_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; 
lean_dec(v_a_2849_);
v___x_2888_ = lean_box(0);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; lean_object* v_pat_2890_; 
v___x_2889_ = lean_unsigned_to_nat(1u);
v_pat_2890_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2889_);
lean_dec(v_a_2849_);
v_a_2849_ = v_pat_2890_;
goto _start;
}
}
else
{
lean_object* v___x_2892_; lean_object* v_h_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2892_ = lean_unsigned_to_nat(1u);
v_h_2893_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2892_);
lean_dec(v_a_2849_);
v___x_2894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2894_, 0, v_h_2893_);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2894_);
return v___x_2895_;
}
}
else
{
lean_object* v___x_2896_; lean_object* v_h_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2896_ = lean_unsigned_to_nat(1u);
v_h_2897_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2896_);
lean_dec(v_a_2849_);
v___x_2898_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2898_, 0, v_h_2897_);
v___x_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2898_);
return v___x_2899_;
}
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2900_);
lean_dec(v_a_2849_);
v___x_2902_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePats___closed__1));
lean_inc(v___x_2901_);
v___x_2903_ = l_Lean_Syntax_isOfKind(v___x_2901_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
lean_dec(v___x_2901_);
v___x_2904_ = lean_box(0);
return v___x_2904_;
}
else
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v___x_2905_ = lean_unsigned_to_nat(0u);
v___x_2906_ = l_Lean_Syntax_getArg(v___x_2901_, v___x_2905_);
lean_dec(v___x_2901_);
v___x_2907_ = l_Lean_Syntax_getArgs(v___x_2906_);
lean_dec(v___x_2906_);
v___x_2908_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___x_2909_ = lean_array_get_size(v___x_2907_);
v___x_2910_ = lean_nat_dec_lt(v___x_2905_, v___x_2909_);
if (v___x_2910_ == 0)
{
lean_dec_ref(v___x_2907_);
v___y_2851_ = v___x_2908_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = lean_box(v___x_2903_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2908_);
v___x_2913_ = lean_nat_dec_le(v___x_2909_, v___x_2909_);
if (v___x_2913_ == 0)
{
if (v___x_2910_ == 0)
{
lean_dec_ref(v___x_2912_);
lean_dec_ref(v___x_2907_);
v___y_2851_ = v___x_2908_;
goto v___jp_2850_;
}
else
{
size_t v___x_2914_; size_t v___x_2915_; lean_object* v___x_2916_; lean_object* v_snd_2917_; 
v___x_2914_ = ((size_t)0ULL);
v___x_2915_ = lean_usize_of_nat(v___x_2909_);
v___x_2916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2903_, v___x_2879_, v___x_2907_, v___x_2914_, v___x_2915_, v___x_2912_);
lean_dec_ref(v___x_2907_);
v_snd_2917_ = lean_ctor_get(v___x_2916_, 1);
lean_inc(v_snd_2917_);
lean_dec_ref(v___x_2916_);
v___y_2851_ = v_snd_2917_;
goto v___jp_2850_;
}
}
else
{
size_t v___x_2918_; size_t v___x_2919_; lean_object* v___x_2920_; lean_object* v_snd_2921_; 
v___x_2918_ = ((size_t)0ULL);
v___x_2919_ = lean_usize_of_nat(v___x_2909_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2903_, v___x_2879_, v___x_2907_, v___x_2918_, v___x_2919_, v___x_2912_);
lean_dec_ref(v___x_2907_);
v_snd_2921_ = lean_ctor_get(v___x_2920_, 1);
lean_inc(v_snd_2921_);
lean_dec_ref(v___x_2920_);
v___y_2851_ = v_snd_2921_;
goto v___jp_2850_;
}
}
}
}
}
else
{
lean_object* v___x_2922_; lean_object* v_name_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v_name_2923_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2922_);
lean_dec(v_a_2849_);
v___x_2924_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2924_, 0, v_name_2923_);
v___x_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
}
else
{
lean_object* v___x_2926_; lean_object* v_name_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v___x_2926_ = lean_unsigned_to_nat(0u);
v_name_2927_ = l_Lean_Syntax_getArg(v_a_2849_, v___x_2926_);
lean_dec(v_a_2849_);
v___x_2928_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2927_);
v___x_2929_ = l_Lean_Syntax_isOfKind(v_name_2927_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
lean_dec(v_name_2927_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2931_, 0, v_name_2927_);
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2931_);
return v___x_2932_;
}
}
v___jp_2850_:
{
size_t v_sz_2852_; size_t v___x_2853_; lean_object* v___x_2854_; 
v_sz_2852_ = lean_array_size(v___y_2851_);
v___x_2853_ = ((size_t)0ULL);
v___x_2854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_2852_, v___x_2853_, v___y_2851_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_box(0);
return v___x_2855_;
}
else
{
lean_object* v_val_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2875_; 
v_val_2856_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2858_ = v___x_2854_;
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_val_2856_);
lean_dec(v___x_2854_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2875_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
size_t v_sz_2860_; lean_object* v___x_2861_; 
v_sz_2860_ = lean_array_size(v_val_2856_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_2860_, v___x_2853_, v_val_2856_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v___x_2862_; 
lean_del_object(v___x_2858_);
v___x_2862_ = lean_box(0);
return v___x_2862_;
}
else
{
lean_object* v_val_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2874_; 
v_val_2863_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2865_ = v___x_2861_;
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_val_2863_);
lean_dec(v___x_2861_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2869_; 
v___x_2867_ = lean_array_to_list(v_val_2863_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2867_);
v___x_2869_ = v___x_2858_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2871_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2869_);
v___x_2871_ = v___x_2865_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(size_t v_sz_2933_, size_t v_i_2934_, lean_object* v_bs_2935_){
_start:
{
uint8_t v___x_2936_; 
v___x_2936_ = lean_usize_dec_lt(v_i_2934_, v_sz_2933_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v_bs_2935_);
return v___x_2937_;
}
else
{
lean_object* v_v_2938_; lean_object* v___x_2939_; 
v_v_2938_ = lean_array_uget_borrowed(v_bs_2935_, v_i_2934_);
lean_inc(v_v_2938_);
v___x_2939_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_v_2938_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2940_; 
lean_dec_ref(v_bs_2935_);
v___x_2940_ = lean_box(0);
return v___x_2940_;
}
else
{
lean_object* v_val_2941_; lean_object* v___x_2942_; lean_object* v_bs_x27_2943_; size_t v___x_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v_val_2941_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_val_2941_);
lean_dec_ref(v___x_2939_);
v___x_2942_ = lean_unsigned_to_nat(0u);
v_bs_x27_2943_ = lean_array_uset(v_bs_2935_, v_i_2934_, v___x_2942_);
v___x_2944_ = ((size_t)1ULL);
v___x_2945_ = lean_usize_add(v_i_2934_, v___x_2944_);
v___x_2946_ = lean_array_uset(v_bs_x27_2943_, v_i_2934_, v_val_2941_);
v_i_2934_ = v___x_2945_;
v_bs_2935_ = v___x_2946_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1___boxed(lean_object* v_sz_2948_, lean_object* v_i_2949_, lean_object* v_bs_2950_){
_start:
{
size_t v_sz_boxed_2951_; size_t v_i_boxed_2952_; lean_object* v_res_2953_; 
v_sz_boxed_2951_ = lean_unbox_usize(v_sz_2948_);
lean_dec(v_sz_2948_);
v_i_boxed_2952_ = lean_unbox_usize(v_i_2949_);
lean_dec(v_i_2949_);
v_res_2953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_boxed_2951_, v_i_boxed_2952_, v_bs_2950_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse(lean_object* v_pat_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v___f_2957_; lean_object* v___x_2958_; 
v___f_2957_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2955_);
v___x_2958_ = l_Lean_expandMacros(v_pat_2954_, v___f_2957_, v_a_2955_, v_a_2956_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2970_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_a_2960_ = lean_ctor_get(v___x_2958_, 1);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2962_ = v___x_2958_;
v_isShared_2963_ = v_isSharedCheck_2970_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2970_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_a_2959_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; 
lean_del_object(v___x_2962_);
v___x_2965_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2960_);
return v___x_2965_;
}
else
{
lean_object* v_val_2966_; lean_object* v___x_2968_; 
v_val_2966_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_val_2966_);
lean_dec_ref(v___x_2964_);
if (v_isShared_2963_ == 0)
{
lean_ctor_set(v___x_2962_, 0, v_val_2966_);
v___x_2968_ = v___x_2962_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_val_2966_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_a_2960_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
v_a_2971_ = lean_ctor_get(v___x_2958_, 0);
v_a_2972_ = lean_ctor_get(v___x_2958_, 1);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2958_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_inc(v_a_2971_);
lean_dec(v___x_2958_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2971_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse___boxed(lean_object* v_pat_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_Lean_Parser_Tactic_MRefinePat_parse(v_pat_2980_, v_a_2981_, v_a_2982_);
lean_dec_ref(v_a_2981_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(lean_object* v_x_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_){
_start:
{
lean_object* v___x_3017_; uint8_t v___x_3018_; 
v___x_3017_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefineError___closed__1));
v___x_3018_ = l_Lean_Syntax_isOfKind(v_x_3014_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3019_ = lean_box(1);
v___x_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
lean_ctor_set(v___x_3020_, 1, v_a_3016_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3021_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0));
v___x_3022_ = l_Lean_Macro_throwError___redArg(v___x_3021_, v_a_3015_, v_a_3016_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
v_a_3024_ = lean_ctor_get(v___x_3022_, 1);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3022_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_inc(v_a_3023_);
lean_dec(v___x_3022_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3023_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
v_a_3032_ = lean_ctor_get(v___x_3022_, 0);
v_a_3033_ = lean_ctor_get(v___x_3022_, 1);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3022_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_inc(v_a_3032_);
lean_dec(v___x_3022_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3032_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___boxed(lean_object* v_x_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(v_x_3041_, v_a_3042_, v_a_3043_);
lean_dec_ref(v_a_3042_);
return v_res_3044_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mintroPat(void){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_box(0);
return v___x_3074_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4(void){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3095_ = l_Lean_binderIdent;
v___x_3096_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3));
v___x_3097_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3098_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
lean_ctor_set(v___x_3098_, 1, v___x_3096_);
lean_ctor_set(v___x_3098_, 2, v___x_3095_);
return v___x_3098_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5(void){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3099_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4);
v___x_3100_ = lean_unsigned_to_nat(1022u);
v___x_3101_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1));
v___x_3102_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3101_);
lean_ctor_set(v___x_3102_, 1, v___x_3100_);
lean_ctor_set(v___x_3102_, 2, v___x_3099_);
return v___x_3102_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200__(void){
_start:
{
lean_object* v___x_3103_; 
v___x_3103_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(lean_object* v_x_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_){
_start:
{
lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3144_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroError___closed__1));
v___x_3145_ = l_Lean_Syntax_isOfKind(v_x_3141_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_box(1);
v___x_3147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3146_);
lean_ctor_set(v___x_3147_, 1, v_a_3143_);
return v___x_3147_;
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0));
v___x_3149_ = l_Lean_Macro_throwError___redArg(v___x_3148_, v_a_3142_, v_a_3143_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_a_3151_ = lean_ctor_get(v___x_3149_, 1);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3149_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3150_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3159_ = lean_ctor_get(v___x_3149_, 0);
v_a_3160_ = lean_ctor_get(v___x_3149_, 1);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3149_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_inc(v_a_3159_);
lean_dec(v___x_3149_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3159_);
lean_ctor_set(v_reuseFailAlloc_3166_, 1, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___boxed(lean_object* v_x_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_){
_start:
{
lean_object* v_res_3171_; 
v_res_3171_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(v_x_3168_, v_a_3169_, v_a_3170_);
lean_dec_ref(v_a_3169_);
return v_res_3171_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2));
v___x_3180_ = l_String_toRawSubstring_x27(v___x_3179_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3188_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__0));
v___x_3189_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__1));
lean_inc(v_x_3185_);
v___x_3190_ = l_Lean_Syntax_isOfKind(v_x_3185_, v___x_3189_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec(v_x_3185_);
v___x_3191_ = lean_box(1);
v___x_3192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_a_3187_);
return v___x_3192_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3193_ = lean_unsigned_to_nat(0u);
v___x_3194_ = lean_unsigned_to_nat(1u);
v___x_3195_ = l_Lean_Syntax_getArg(v_x_3185_, v___x_3194_);
lean_dec(v_x_3185_);
v___x_3196_ = lean_unsigned_to_nat(2u);
v___x_3197_ = l_Lean_Syntax_getNumArgs(v___x_3195_);
v___x_3198_ = lean_nat_dec_le(v___x_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
uint8_t v___x_3199_; 
lean_dec(v___x_3197_);
lean_inc(v___x_3195_);
v___x_3199_ = l_Lean_Syntax_matchesNull(v___x_3195_, v___x_3194_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec(v___x_3195_);
v___x_3200_ = lean_box(1);
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v_a_3187_);
return v___x_3201_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; 
v___x_3202_ = l_Lean_Syntax_getArg(v___x_3195_, v___x_3193_);
lean_dec(v___x_3195_);
v___x_3203_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat___00__closed__1));
lean_inc(v___x_3202_);
v___x_3204_ = l_Lean_Syntax_isOfKind(v___x_3202_, v___x_3203_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
lean_dec(v___x_3202_);
v___x_3205_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3187_);
return v___x_3205_;
}
else
{
lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3206_ = l_Lean_Syntax_getArg(v___x_3202_, v___x_3193_);
lean_dec(v___x_3202_);
v___x_3207_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
lean_inc(v___x_3206_);
v___x_3208_ = l_Lean_Syntax_isOfKind(v___x_3206_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v_quotContext_3209_; lean_object* v_currMacroScope_3210_; lean_object* v_ref_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_quotContext_3209_ = lean_ctor_get(v_a_3186_, 1);
v_currMacroScope_3210_ = lean_ctor_get(v_a_3186_, 2);
v_ref_3211_ = lean_ctor_get(v_a_3186_, 5);
v___x_3212_ = l_Lean_SourceInfo_fromRef(v_ref_3211_, v___x_3208_);
v___x_3213_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3214_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3212_, 12);
v___x_3215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3212_);
lean_ctor_set(v___x_3215_, 1, v___x_3188_);
v___x_3216_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3217_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3218_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3210_);
lean_inc(v_quotContext_3209_);
v___x_3219_ = l_Lean_addMacroScope(v_quotContext_3209_, v___x_3218_, v_currMacroScope_3210_);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3212_);
lean_ctor_set(v___x_3221_, 1, v___x_3217_);
lean_ctor_set(v___x_3221_, 2, v___x_3219_);
lean_ctor_set(v___x_3221_, 3, v___x_3220_);
lean_inc_ref(v___x_3221_);
v___x_3222_ = l_Lean_Syntax_node1(v___x_3212_, v___x_3216_, v___x_3221_);
v___x_3223_ = l_Lean_Syntax_node1(v___x_3212_, v___x_3207_, v___x_3222_);
v___x_3224_ = l_Lean_Syntax_node1(v___x_3212_, v___x_3203_, v___x_3223_);
v___x_3225_ = l_Lean_Syntax_node1(v___x_3212_, v___x_3214_, v___x_3224_);
v___x_3226_ = l_Lean_Syntax_node2(v___x_3212_, v___x_3189_, v___x_3215_, v___x_3225_);
v___x_3227_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3212_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3230_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3231_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3212_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
v___x_3232_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3212_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_Syntax_node4(v___x_3212_, v___x_3230_, v___x_3231_, v___x_3221_, v___x_3233_, v___x_3206_);
v___x_3235_ = l_Lean_Syntax_node3(v___x_3212_, v___x_3214_, v___x_3226_, v___x_3228_, v___x_3234_);
v___x_3236_ = l_Lean_Syntax_node1(v___x_3212_, v___x_3213_, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v_a_3187_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v___x_3238_ = l_Lean_Syntax_getArg(v___x_3206_, v___x_3193_);
v___x_3239_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3240_ = l_Lean_Syntax_isOfKind(v___x_3238_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v_quotContext_3241_; lean_object* v_currMacroScope_3242_; lean_object* v_ref_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_quotContext_3241_ = lean_ctor_get(v_a_3186_, 1);
v_currMacroScope_3242_ = lean_ctor_get(v_a_3186_, 2);
v_ref_3243_ = lean_ctor_get(v_a_3186_, 5);
v___x_3244_ = l_Lean_SourceInfo_fromRef(v_ref_3243_, v___x_3240_);
v___x_3245_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3246_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3244_, 12);
v___x_3247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3244_);
lean_ctor_set(v___x_3247_, 1, v___x_3188_);
v___x_3248_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3249_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3242_);
lean_inc(v_quotContext_3241_);
v___x_3250_ = l_Lean_addMacroScope(v_quotContext_3241_, v___x_3249_, v_currMacroScope_3242_);
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3244_);
lean_ctor_set(v___x_3252_, 1, v___x_3248_);
lean_ctor_set(v___x_3252_, 2, v___x_3250_);
lean_ctor_set(v___x_3252_, 3, v___x_3251_);
lean_inc_ref(v___x_3252_);
v___x_3253_ = l_Lean_Syntax_node1(v___x_3244_, v___x_3239_, v___x_3252_);
v___x_3254_ = l_Lean_Syntax_node1(v___x_3244_, v___x_3207_, v___x_3253_);
v___x_3255_ = l_Lean_Syntax_node1(v___x_3244_, v___x_3203_, v___x_3254_);
v___x_3256_ = l_Lean_Syntax_node1(v___x_3244_, v___x_3246_, v___x_3255_);
v___x_3257_ = l_Lean_Syntax_node2(v___x_3244_, v___x_3189_, v___x_3247_, v___x_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3244_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
v___x_3260_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3261_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3262_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3244_);
lean_ctor_set(v___x_3262_, 1, v___x_3260_);
v___x_3263_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3244_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = l_Lean_Syntax_node4(v___x_3244_, v___x_3261_, v___x_3262_, v___x_3252_, v___x_3264_, v___x_3206_);
v___x_3266_ = l_Lean_Syntax_node3(v___x_3244_, v___x_3246_, v___x_3257_, v___x_3259_, v___x_3265_);
v___x_3267_ = l_Lean_Syntax_node1(v___x_3244_, v___x_3245_, v___x_3266_);
v___x_3268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
lean_ctor_set(v___x_3268_, 1, v_a_3187_);
return v___x_3268_;
}
else
{
lean_object* v___x_3269_; 
lean_dec(v___x_3206_);
v___x_3269_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3187_);
return v___x_3269_;
}
}
}
}
}
else
{
lean_object* v_ref_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v_pats_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v_ref_3270_ = lean_ctor_get(v_a_3186_, 5);
v___x_3271_ = l_Lean_Syntax_getArg(v___x_3195_, v___x_3193_);
v___x_3272_ = l_Lean_Syntax_getArg(v___x_3195_, v___x_3194_);
v___x_3273_ = l_Lean_Syntax_getArgs(v___x_3195_);
lean_dec(v___x_3195_);
v___x_3274_ = l_Array_extract___redArg(v___x_3273_, v___x_3196_, v___x_3197_);
lean_dec_ref(v___x_3273_);
v___x_3275_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3276_ = lean_box(2);
v___x_3277_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v___x_3275_);
lean_ctor_set(v___x_3277_, 2, v___x_3274_);
v_pats_3278_ = l_Lean_Syntax_getArgs(v___x_3277_);
lean_dec_ref(v___x_3277_);
v___x_3279_ = 0;
v___x_3280_ = l_Lean_SourceInfo_fromRef(v_ref_3270_, v___x_3279_);
v___x_3281_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3280_, 7);
v___x_3282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3188_);
v___x_3283_ = l_Lean_Syntax_node1(v___x_3280_, v___x_3275_, v___x_3271_);
lean_inc_ref(v___x_3282_);
v___x_3284_ = l_Lean_Syntax_node2(v___x_3280_, v___x_3189_, v___x_3282_, v___x_3283_);
v___x_3285_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3280_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Array_mkArray1___redArg(v___x_3272_);
v___x_3288_ = l_Array_append___redArg(v___x_3287_, v_pats_3278_);
lean_dec_ref(v_pats_3278_);
v___x_3289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3280_);
lean_ctor_set(v___x_3289_, 1, v___x_3275_);
lean_ctor_set(v___x_3289_, 2, v___x_3288_);
v___x_3290_ = l_Lean_Syntax_node2(v___x_3280_, v___x_3189_, v___x_3282_, v___x_3289_);
v___x_3291_ = l_Lean_Syntax_node3(v___x_3280_, v___x_3275_, v___x_3284_, v___x_3286_, v___x_3290_);
v___x_3292_ = l_Lean_Syntax_node1(v___x_3280_, v___x_3281_, v___x_3291_);
v___x_3293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
lean_ctor_set(v___x_3293_, 1, v_a_3187_);
return v___x_3293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object* v_x_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(v_x_3294_, v_a_3295_, v_a_3296_);
lean_dec_ref(v_a_3295_);
return v_res_3297_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrevertPat(void){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_box(0);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(lean_object* v_x_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevertError___closed__1));
v___x_3403_ = l_Lean_Syntax_isOfKind(v_x_3399_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_box(1);
v___x_3405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v_a_3401_);
return v___x_3405_;
}
else
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0));
v___x_3407_ = l_Lean_Macro_throwError___redArg(v___x_3406_, v_a_3400_, v_a_3401_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_a_3409_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3407_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3408_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
v_a_3417_ = lean_ctor_get(v___x_3407_, 0);
v_a_3418_ = lean_ctor_get(v___x_3407_, 1);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3407_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_inc(v_a_3417_);
lean_dec(v___x_3407_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3417_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___boxed(lean_object* v_x_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(v_x_3426_, v_a_3427_, v_a_3428_);
lean_dec_ref(v_a_3427_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(lean_object* v_x_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3433_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__0));
v___x_3434_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__1));
lean_inc(v_x_3430_);
v___x_3435_ = l_Lean_Syntax_isOfKind(v_x_3430_, v___x_3434_);
if (v___x_3435_ == 0)
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
lean_dec(v_x_3430_);
v___x_3436_ = lean_box(1);
v___x_3437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v_a_3432_);
return v___x_3437_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; 
v___x_3438_ = lean_unsigned_to_nat(1u);
v___x_3439_ = l_Lean_Syntax_getArg(v_x_3430_, v___x_3438_);
lean_dec(v_x_3430_);
v___x_3440_ = lean_unsigned_to_nat(2u);
v___x_3441_ = l_Lean_Syntax_getNumArgs(v___x_3439_);
v___x_3442_ = lean_nat_dec_le(v___x_3440_, v___x_3441_);
if (v___x_3442_ == 0)
{
lean_object* v___x_3443_; lean_object* v___x_3444_; 
lean_dec(v___x_3441_);
lean_dec(v___x_3439_);
v___x_3443_ = lean_box(1);
v___x_3444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3443_);
lean_ctor_set(v___x_3444_, 1, v_a_3432_);
return v___x_3444_;
}
else
{
lean_object* v_ref_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v_pats_3454_; uint8_t v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_ref_3445_ = lean_ctor_get(v_a_3431_, 5);
v___x_3446_ = lean_unsigned_to_nat(0u);
v___x_3447_ = l_Lean_Syntax_getArg(v___x_3439_, v___x_3446_);
v___x_3448_ = l_Lean_Syntax_getArg(v___x_3439_, v___x_3438_);
v___x_3449_ = l_Lean_Syntax_getArgs(v___x_3439_);
lean_dec(v___x_3439_);
v___x_3450_ = l_Array_extract___redArg(v___x_3449_, v___x_3440_, v___x_3441_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3452_ = lean_box(2);
v___x_3453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3452_);
lean_ctor_set(v___x_3453_, 1, v___x_3451_);
lean_ctor_set(v___x_3453_, 2, v___x_3450_);
v_pats_3454_ = l_Lean_Syntax_getArgs(v___x_3453_);
lean_dec_ref(v___x_3453_);
v___x_3455_ = 0;
v___x_3456_ = l_Lean_SourceInfo_fromRef(v_ref_3445_, v___x_3455_);
v___x_3457_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3456_, 7);
v___x_3458_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3433_);
v___x_3459_ = l_Lean_Syntax_node1(v___x_3456_, v___x_3451_, v___x_3447_);
lean_inc_ref(v___x_3458_);
v___x_3460_ = l_Lean_Syntax_node2(v___x_3456_, v___x_3434_, v___x_3458_, v___x_3459_);
v___x_3461_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3456_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = l_Array_mkArray1___redArg(v___x_3448_);
v___x_3464_ = l_Array_append___redArg(v___x_3463_, v_pats_3454_);
lean_dec_ref(v_pats_3454_);
v___x_3465_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3456_);
lean_ctor_set(v___x_3465_, 1, v___x_3451_);
lean_ctor_set(v___x_3465_, 2, v___x_3464_);
v___x_3466_ = l_Lean_Syntax_node2(v___x_3456_, v___x_3434_, v___x_3458_, v___x_3465_);
v___x_3467_ = l_Lean_Syntax_node3(v___x_3456_, v___x_3451_, v___x_3460_, v___x_3462_, v___x_3466_);
v___x_3468_ = l_Lean_Syntax_node1(v___x_3456_, v___x_3457_, v___x_3467_);
v___x_3469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3468_);
lean_ctor_set(v___x_3469_, 1, v_a_3432_);
return v___x_3469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1___boxed(lean_object* v_x_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(v_x_3470_, v_a_3471_, v_a_3472_);
lean_dec_ref(v_a_3471_);
return v_res_3473_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7));
v___x_3540_ = lean_mk_syntax_ident(v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(lean_object* v_x_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3570_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3613_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
lean_inc(v_x_3542_);
v___x_3614_ = l_Lean_Syntax_isOfKind(v_x_3542_, v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
lean_dec(v_x_3542_);
v___x_3615_ = lean_box(1);
v___x_3616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3615_);
lean_ctor_set(v___x_3616_, 1, v_a_3544_);
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = lean_unsigned_to_nat(1u);
v___x_3618_ = l_Lean_Syntax_getArg(v_x_3542_, v___x_3617_);
lean_dec(v_x_3542_);
v___x_3619_ = l_Lean_Syntax_getOptional_x3f(v___x_3618_);
lean_dec(v___x_3618_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_box(0);
v___y_3570_ = v___x_3620_;
goto v___jp_3569_;
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_val_3621_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3619_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_val_3621_);
lean_dec(v___x_3619_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_val_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
v___y_3570_ = v___x_3626_;
goto v___jp_3569_;
}
}
}
}
v___jp_3545_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_inc_ref(v___y_3558_);
v___x_3560_ = l_Array_append___redArg(v___y_3558_, v___y_3559_);
lean_dec_ref(v___y_3559_);
lean_inc(v___y_3546_);
lean_inc_n(v___y_3554_, 6);
v___x_3561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3561_, 0, v___y_3554_);
lean_ctor_set(v___x_3561_, 1, v___y_3546_);
lean_ctor_set(v___x_3561_, 2, v___x_3560_);
v___x_3562_ = l_Lean_Syntax_node2(v___y_3554_, v___y_3551_, v___y_3556_, v___x_3561_);
lean_inc(v___y_3557_);
v___x_3563_ = l_Lean_Syntax_node3(v___y_3554_, v___y_3557_, v___y_3548_, v___y_3552_, v___x_3562_);
v___x_3564_ = l_Lean_Syntax_node1(v___y_3554_, v___y_3546_, v___x_3563_);
v___x_3565_ = l_Lean_Syntax_node1(v___y_3554_, v___y_3550_, v___x_3564_);
v___x_3566_ = l_Lean_Syntax_node1(v___y_3554_, v___y_3547_, v___x_3565_);
v___x_3567_ = l_Lean_Syntax_node3(v___y_3554_, v___y_3555_, v___y_3549_, v___x_3566_, v___y_3553_);
v___x_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
lean_ctor_set(v___x_3568_, 1, v_a_3544_);
return v___x_3568_;
}
v___jp_3569_:
{
lean_object* v_ref_3571_; uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_ref_3571_ = lean_ctor_get(v_a_3543_, 5);
v___x_3572_ = 0;
v___x_3573_ = l_Lean_SourceInfo_fromRef(v_ref_3571_, v___x_3572_);
v___x_3574_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3575_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3573_, 20);
v___x_3576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3573_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3578_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3579_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3580_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1));
v___x_3581_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3582_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3573_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3));
v___x_3585_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4));
v___x_3586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3573_);
lean_ctor_set(v___x_3586_, 1, v___x_3585_);
v___x_3587_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__1));
v___x_3588_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__2));
v___x_3589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3573_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8);
v___x_3591_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3579_, v___x_3590_);
lean_inc_ref(v___x_3589_);
v___x_3592_ = l_Lean_Syntax_node2(v___x_3573_, v___x_3587_, v___x_3589_, v___x_3591_);
v___x_3593_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3579_, v___x_3592_);
v___x_3594_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3578_, v___x_3593_);
v___x_3595_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3577_, v___x_3594_);
v___x_3596_ = l_Lean_Syntax_node2(v___x_3573_, v___x_3584_, v___x_3586_, v___x_3595_);
v___x_3597_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3579_, v___x_3596_);
v___x_3598_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3578_, v___x_3597_);
v___x_3599_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3577_, v___x_3598_);
v___x_3600_ = l_Lean_Syntax_node2(v___x_3573_, v___x_3581_, v___x_3583_, v___x_3599_);
v___x_3601_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3579_, v___x_3600_);
v___x_3602_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3578_, v___x_3601_);
v___x_3603_ = l_Lean_Syntax_node1(v___x_3573_, v___x_3577_, v___x_3602_);
v___x_3604_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3573_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
lean_inc_ref(v___x_3605_);
lean_inc_ref(v___x_3576_);
v___x_3606_ = l_Lean_Syntax_node3(v___x_3573_, v___x_3574_, v___x_3576_, v___x_3603_, v___x_3605_);
v___x_3607_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9));
v___x_3608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3573_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3570_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3611_; 
v_val_3610_ = lean_ctor_get(v___y_3570_, 0);
lean_inc(v_val_3610_);
lean_dec_ref(v___y_3570_);
v___x_3611_ = l_Array_mkArray1___redArg(v_val_3610_);
v___y_3546_ = v___x_3579_;
v___y_3547_ = v___x_3577_;
v___y_3548_ = v___x_3606_;
v___y_3549_ = v___x_3576_;
v___y_3550_ = v___x_3578_;
v___y_3551_ = v___x_3587_;
v___y_3552_ = v___x_3608_;
v___y_3553_ = v___x_3605_;
v___y_3554_ = v___x_3573_;
v___y_3555_ = v___x_3574_;
v___y_3556_ = v___x_3589_;
v___y_3557_ = v___x_3580_;
v___y_3558_ = v___x_3609_;
v___y_3559_ = v___x_3611_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3612_; 
lean_dec(v___y_3570_);
v___x_3612_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3546_ = v___x_3579_;
v___y_3547_ = v___x_3577_;
v___y_3548_ = v___x_3606_;
v___y_3549_ = v___x_3576_;
v___y_3550_ = v___x_3578_;
v___y_3551_ = v___x_3587_;
v___y_3552_ = v___x_3608_;
v___y_3553_ = v___x_3605_;
v___y_3554_ = v___x_3573_;
v___y_3555_ = v___x_3574_;
v___y_3556_ = v___x_3589_;
v___y_3557_ = v___x_3580_;
v___y_3558_ = v___x_3609_;
v___y_3559_ = v___x_3612_;
goto v___jp_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___boxed(lean_object* v_x_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(v_x_3629_, v_a_3630_, v_a_3631_);
lean_dec_ref(v_a_3630_);
return v_res_3632_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4));
v___x_3665_ = lean_mk_syntax_ident(v___x_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(lean_object* v_x_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3761_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3778_ = ((lean_object*)(l_Lean_Parser_Tactic_mspec___closed__1));
lean_inc(v_x_3673_);
v___x_3779_ = l_Lean_Syntax_isOfKind(v_x_3673_, v___x_3778_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_dec(v_x_3673_);
v___x_3780_ = lean_box(1);
v___x_3781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v_a_3675_);
return v___x_3781_;
}
else
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = lean_unsigned_to_nat(1u);
v___x_3783_ = l_Lean_Syntax_getArg(v_x_3673_, v___x_3782_);
lean_dec(v_x_3673_);
v___x_3784_ = l_Lean_Syntax_getOptional_x3f(v___x_3783_);
lean_dec(v___x_3783_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_box(0);
v___y_3761_ = v___x_3785_;
goto v___jp_3760_;
}
else
{
lean_object* v_val_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_val_3786_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3784_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_val_3786_);
lean_dec(v___x_3784_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_val_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
v___y_3761_ = v___x_3791_;
goto v___jp_3760_;
}
}
}
}
v___jp_3676_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
lean_inc_ref_n(v___y_3678_, 2);
v___x_3687_ = l_Array_append___redArg(v___y_3678_, v___y_3686_);
lean_dec_ref(v___y_3686_);
lean_inc_n(v___y_3683_, 12);
lean_inc_n(v___y_3682_, 50);
v___x_3688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3688_, 0, v___y_3682_);
lean_ctor_set(v___x_3688_, 1, v___y_3683_);
lean_ctor_set(v___x_3688_, 2, v___x_3687_);
lean_inc(v___y_3684_);
v___x_3689_ = l_Lean_Syntax_node2(v___y_3682_, v___y_3684_, v___y_3679_, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3690_, 0, v___y_3682_);
lean_ctor_set(v___x_3690_, 1, v___y_3683_);
lean_ctor_set(v___x_3690_, 2, v___y_3678_);
v___x_3691_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1));
v___x_3692_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2));
v___x_3693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___y_3682_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3695_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___y_3682_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12));
v___x_3698_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13));
v___x_3699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___y_3682_);
lean_ctor_set(v___x_3699_, 1, v___x_3697_);
v___x_3700_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15));
lean_inc_ref_n(v___x_3690_, 8);
v___x_3701_ = l_Lean_Syntax_node1(v___y_3682_, v___x_3700_, v___x_3690_);
v___x_3702_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17));
v___x_3703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___y_3682_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3683_, v___x_3703_);
v___x_3705_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_3706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___y_3682_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20));
v___x_3708_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5);
v___x_3709_ = l_Lean_Syntax_node3(v___y_3682_, v___x_3707_, v___x_3690_, v___x_3690_, v___x_3708_);
v___x_3710_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_3711_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3711_, 0, v___y_3682_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29);
v___x_3713_ = l_Lean_Syntax_node3(v___y_3682_, v___x_3707_, v___x_3690_, v___x_3690_, v___x_3712_);
v___x_3714_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3683_, v___x_3709_, v___x_3711_, v___x_3713_);
v___x_3715_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156));
v___x_3716_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___y_3682_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3683_, v___x_3706_, v___x_3714_, v___x_3716_);
v___x_3718_ = l_Lean_Syntax_node6(v___y_3682_, v___x_3698_, v___x_3699_, v___x_3701_, v___x_3690_, v___x_3704_, v___x_3717_, v___x_3690_);
v___x_3719_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3683_, v___x_3718_);
lean_inc_n(v___y_3677_, 7);
v___x_3720_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3719_);
lean_inc_n(v___y_3680_, 7);
v___x_3721_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3720_);
lean_inc_ref(v___x_3696_);
v___x_3722_ = l_Lean_Syntax_node2(v___y_3682_, v___x_3694_, v___x_3696_, v___x_3721_);
v___x_3723_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3683_, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3723_);
v___x_3725_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3724_);
v___x_3726_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___y_3682_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
lean_inc_ref_n(v___x_3727_, 3);
lean_inc_n(v___y_3685_, 3);
lean_inc_n(v___y_3681_, 4);
v___x_3728_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3681_, v___y_3685_, v___x_3725_, v___x_3727_);
v___x_3729_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3730_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___y_3682_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = l_Lean_Syntax_node1(v___y_3682_, v___x_3729_, v___x_3731_);
v___x_3733_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___y_3682_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3736_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3737_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___y_3682_);
lean_ctor_set(v___x_3737_, 1, v___x_3736_);
v___x_3738_ = l_Lean_Syntax_node1(v___y_3682_, v___x_3735_, v___x_3737_);
v___x_3739_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3683_, v___x_3732_, v___x_3734_, v___x_3738_);
v___x_3740_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3739_);
v___x_3741_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node2(v___y_3682_, v___x_3694_, v___x_3696_, v___x_3741_);
v___x_3743_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3683_, v___x_3742_);
v___x_3744_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3743_);
v___x_3745_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3744_);
v___x_3746_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3681_, v___y_3685_, v___x_3745_, v___x_3727_);
v___x_3747_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3683_, v___x_3728_, v___x_3690_, v___x_3746_);
v___x_3748_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3747_);
v___x_3749_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3748_);
v___x_3750_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3681_, v___y_3685_, v___x_3749_, v___x_3727_);
v___x_3751_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3683_, v___x_3750_);
v___x_3752_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3751_);
v___x_3753_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3752_);
v___x_3754_ = l_Lean_Syntax_node2(v___y_3682_, v___x_3691_, v___x_3693_, v___x_3753_);
v___x_3755_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3683_, v___x_3689_, v___x_3690_, v___x_3754_);
v___x_3756_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3677_, v___x_3755_);
v___x_3757_ = l_Lean_Syntax_node1(v___y_3682_, v___y_3680_, v___x_3756_);
v___x_3758_ = l_Lean_Syntax_node3(v___y_3682_, v___y_3681_, v___y_3685_, v___x_3757_, v___x_3727_);
v___x_3759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
lean_ctor_set(v___x_3759_, 1, v_a_3675_);
return v___x_3759_;
}
v___jp_3760_:
{
lean_object* v_ref_3762_; uint8_t v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v_ref_3762_ = lean_ctor_get(v_a_3674_, 5);
v___x_3763_ = 0;
v___x_3764_ = l_Lean_SourceInfo_fromRef(v_ref_3762_, v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3766_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3764_, 2);
v___x_3767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3764_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3769_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3770_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3771_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
v___x_3772_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__2));
v___x_3773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3764_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3761_) == 1)
{
lean_object* v_val_3775_; lean_object* v___x_3776_; 
v_val_3775_ = lean_ctor_get(v___y_3761_, 0);
lean_inc(v_val_3775_);
lean_dec_ref(v___y_3761_);
v___x_3776_ = l_Array_mkArray1___redArg(v_val_3775_);
v___y_3677_ = v___x_3769_;
v___y_3678_ = v___x_3774_;
v___y_3679_ = v___x_3773_;
v___y_3680_ = v___x_3768_;
v___y_3681_ = v___x_3765_;
v___y_3682_ = v___x_3764_;
v___y_3683_ = v___x_3770_;
v___y_3684_ = v___x_3771_;
v___y_3685_ = v___x_3767_;
v___y_3686_ = v___x_3776_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3777_; 
lean_dec(v___y_3761_);
v___x_3777_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3677_ = v___x_3769_;
v___y_3678_ = v___x_3774_;
v___y_3679_ = v___x_3773_;
v___y_3680_ = v___x_3768_;
v___y_3681_ = v___x_3765_;
v___y_3682_ = v___x_3764_;
v___y_3683_ = v___x_3770_;
v___y_3684_ = v___x_3771_;
v___y_3685_ = v___x_3767_;
v___y_3686_ = v___x_3777_;
goto v___jp_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___boxed(lean_object* v_x_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v_res_3797_; 
v_res_3797_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(v_x_3794_, v_a_3795_, v_a_3796_);
lean_dec_ref(v_a_3795_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(lean_object* v_x_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3841_; uint8_t v___x_3842_; 
v___x_3841_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1));
v___x_3842_ = l_Lean_Syntax_isOfKind(v_x_3838_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_box(1);
v___x_3844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set(v___x_3844_, 1, v_a_3840_);
return v___x_3844_;
}
else
{
lean_object* v_ref_3845_; uint8_t v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_ref_3845_ = lean_ctor_get(v_a_3839_, 5);
v___x_3846_ = 0;
v___x_3847_ = l_Lean_SourceInfo_fromRef(v_ref_3845_, v___x_3846_);
v___x_3848_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0));
v___x_3849_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1));
lean_inc_n(v___x_3847_, 33);
v___x_3850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3847_);
lean_ctor_set(v___x_3850_, 1, v___x_3848_);
v___x_3851_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3852_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3));
v___x_3853_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4));
v___x_3854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3847_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3856_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3857_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3858_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
v___x_3859_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3847_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v___x_3860_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3861_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3847_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___x_3863_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3864_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3847_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3863_, v___x_3865_);
v___x_3867_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3851_, v___x_3866_);
v___x_3868_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3856_, v___x_3867_);
v___x_3869_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3855_, v___x_3868_);
lean_inc_ref(v___x_3862_);
v___x_3870_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3860_, v___x_3862_, v___x_3869_);
v___x_3871_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3851_, v___x_3870_);
v___x_3872_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3856_, v___x_3871_);
v___x_3873_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3855_, v___x_3872_);
v___x_3874_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3847_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = l_Lean_Syntax_node3(v___x_3847_, v___x_3857_, v___x_3859_, v___x_3873_, v___x_3875_);
v___x_3877_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3878_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3847_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3880_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3847_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3879_, v___x_3881_);
v___x_3883_ = l_Lean_Syntax_node3(v___x_3847_, v___x_3851_, v___x_3876_, v___x_3878_, v___x_3882_);
v___x_3884_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3856_, v___x_3883_);
v___x_3885_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3855_, v___x_3884_);
lean_inc_ref(v___x_3854_);
v___x_3886_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3852_, v___x_3854_, v___x_3885_);
v___x_3887_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1));
v___x_3888_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2));
v___x_3889_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3847_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3887_, v___x_3889_);
v___x_3891_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3851_, v___x_3890_);
v___x_3892_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3856_, v___x_3891_);
v___x_3893_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3855_, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3860_, v___x_3862_, v___x_3893_);
v___x_3895_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3851_, v___x_3894_);
v___x_3896_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3856_, v___x_3895_);
v___x_3897_ = l_Lean_Syntax_node1(v___x_3847_, v___x_3855_, v___x_3896_);
v___x_3898_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3852_, v___x_3854_, v___x_3897_);
v___x_3899_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3851_, v___x_3886_, v___x_3898_);
v___x_3900_ = l_Lean_Syntax_node2(v___x_3847_, v___x_3849_, v___x_3850_, v___x_3899_);
v___x_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
lean_ctor_set(v___x_3901_, 1, v_a_3840_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___boxed(lean_object* v_x_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(v_x_3902_, v_a_3903_, v_a_3904_);
lean_dec_ref(v_a_3903_);
return v_res_3905_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__8(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3923_ = l_Lean_cdotTk;
v___x_3924_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__7));
v___x_3925_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3926_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
lean_ctor_set(v___x_3926_, 1, v___x_3924_);
lean_ctor_set(v___x_3926_, 2, v___x_3923_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__13(void){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3936_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_3937_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__8, &l_Lean_Parser_Tactic_invariantDotAlt___closed__8_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__8);
v___x_3938_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3939_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
lean_ctor_set(v___x_3939_, 1, v___x_3937_);
lean_ctor_set(v___x_3939_, 2, v___x_3936_);
return v___x_3939_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__14(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3940_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__13, &l_Lean_Parser_Tactic_invariantDotAlt___closed__13_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__13);
v___x_3941_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__1));
v___x_3942_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__0));
v___x_3943_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
lean_ctor_set(v___x_3943_, 1, v___x_3941_);
lean_ctor_set(v___x_3943_, 2, v___x_3940_);
return v___x_3943_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt(void){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__14, &l_Lean_Parser_Tactic_invariantDotAlt___closed__14_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__14);
return v___x_3944_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5(void){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3958_ = l_Lean_Parser_Tactic_caseArg;
v___x_3959_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__4));
v___x_3960_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3961_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
lean_ctor_set(v___x_3961_, 1, v___x_3959_);
lean_ctor_set(v___x_3961_, 2, v___x_3958_);
return v___x_3961_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__6(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3962_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_3963_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__5, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__5_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5);
v___x_3964_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3965_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
lean_ctor_set(v___x_3965_, 2, v___x_3962_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__7(void){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3966_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_3967_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__6, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__6);
v___x_3968_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3969_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v___x_3967_);
lean_ctor_set(v___x_3969_, 2, v___x_3966_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3970_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__7, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__7_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__7);
v___x_3971_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__1));
v___x_3972_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__0));
v___x_3973_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v___x_3971_);
lean_ctor_set(v___x_3973_, 2, v___x_3970_);
return v___x_3973_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt(void){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__8, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__8_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8);
return v___x_3974_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__4(void){
_start:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = l_Lean_Parser_Tactic_invariantCaseAlt;
v___x_4026_ = l_Lean_Parser_Tactic_invariantDotAlt;
v___x_4027_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4028_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v___x_4026_);
lean_ctor_set(v___x_4028_, 2, v___x_4025_);
return v___x_4028_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__5(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4029_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__4, &l_Lean_Parser_Tactic_invariantAlts___closed__4_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__4);
v___x_4030_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__11));
v___x_4031_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4032_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
lean_ctor_set(v___x_4032_, 1, v___x_4030_);
lean_ctor_set(v___x_4032_, 2, v___x_4029_);
return v___x_4032_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__6(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4033_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__5, &l_Lean_Parser_Tactic_invariantAlts___closed__5_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__5);
v___x_4034_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_4035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v___x_4033_);
return v___x_4035_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__7(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4036_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__6, &l_Lean_Parser_Tactic_invariantAlts___closed__6_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__6);
v___x_4037_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_4038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v___x_4036_);
return v___x_4038_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__8(void){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4039_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__7, &l_Lean_Parser_Tactic_invariantAlts___closed__7_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__7);
v___x_4040_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW));
v___x_4041_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4042_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
lean_ctor_set(v___x_4042_, 1, v___x_4040_);
lean_ctor_set(v___x_4042_, 2, v___x_4039_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__9(void){
_start:
{
lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4043_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__8, &l_Lean_Parser_Tactic_invariantAlts___closed__8_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__8);
v___x_4044_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__1));
v___x_4045_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__0));
v___x_4046_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v___x_4044_);
lean_ctor_set(v___x_4046_, 2, v___x_4043_);
return v___x_4046_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts(void){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__9, &l_Lean_Parser_Tactic_invariantAlts___closed__9_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__9);
return v___x_4047_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__2(void){
_start:
{
uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4054_ = 0;
v___x_4055_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__3));
v___x_4056_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__2));
v___x_4057_ = l_Lean_Parser_Tactic_caseArg;
v___x_4058_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v___x_4056_);
lean_ctor_set(v___x_4058_, 2, v___x_4055_);
lean_ctor_set_uint8(v___x_4058_, sizeof(void*)*3, v___x_4054_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__3(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4059_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__2, &l_Lean_Parser_Tactic_vcAlt___closed__2_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__2);
v___x_4060_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__3));
v___x_4061_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4062_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___x_4060_);
lean_ctor_set(v___x_4062_, 2, v___x_4059_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__4(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_4064_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__3, &l_Lean_Parser_Tactic_vcAlt___closed__3_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__3);
v___x_4065_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4066_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
lean_ctor_set(v___x_4066_, 1, v___x_4064_);
lean_ctor_set(v___x_4066_, 2, v___x_4063_);
return v___x_4066_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__7(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4071_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__6));
v___x_4072_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__4, &l_Lean_Parser_Tactic_vcAlt___closed__4_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__4);
v___x_4073_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4074_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4072_);
lean_ctor_set(v___x_4074_, 2, v___x_4071_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__8(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4075_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__7, &l_Lean_Parser_Tactic_vcAlt___closed__7_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__7);
v___x_4076_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__1));
v___x_4077_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__0));
v___x_4078_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v___x_4076_);
lean_ctor_set(v___x_4078_, 2, v___x_4075_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt(void){
_start:
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__8, &l_Lean_Parser_Tactic_vcAlt___closed__8_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__8);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__10(void){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4106_ = l_Lean_Parser_Tactic_vcAlt;
v___x_4107_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__11));
v___x_4108_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4109_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
lean_ctor_set(v___x_4109_, 1, v___x_4107_);
lean_ctor_set(v___x_4109_, 2, v___x_4106_);
return v___x_4109_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__11(void){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4110_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__10, &l_Lean_Parser_Tactic_vcAlts___closed__10_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__10);
v___x_4111_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_4112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
lean_ctor_set(v___x_4112_, 1, v___x_4110_);
return v___x_4112_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__12(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__11, &l_Lean_Parser_Tactic_vcAlts___closed__11_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__11);
v___x_4114_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_4115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
return v___x_4115_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__13(void){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4116_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__12, &l_Lean_Parser_Tactic_vcAlts___closed__12_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__12);
v___x_4117_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__9));
v___x_4118_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4119_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
lean_ctor_set(v___x_4119_, 1, v___x_4117_);
lean_ctor_set(v___x_4119_, 2, v___x_4116_);
return v___x_4119_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__14(void){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4120_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__13, &l_Lean_Parser_Tactic_vcAlts___closed__13_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__13);
v___x_4121_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__1));
v___x_4122_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__0));
v___x_4123_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v___x_4121_);
lean_ctor_set(v___x_4123_, 2, v___x_4120_);
return v___x_4123_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts(void){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__14, &l_Lean_Parser_Tactic_vcAlts___closed__14_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__14);
return v___x_4124_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__3(void){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4134_ = l_Lean_Parser_Tactic_optConfig;
v___x_4135_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__2));
v___x_4136_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4137_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v___x_4135_);
lean_ctor_set(v___x_4137_, 2, v___x_4134_);
return v___x_4137_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__8(void){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4144_ = l_Lean_Parser_Tactic_simpLemma;
v___x_4145_ = l_Lean_Parser_Tactic_simpErase;
v___x_4146_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4147_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
lean_ctor_set(v___x_4147_, 1, v___x_4145_);
lean_ctor_set(v___x_4147_, 2, v___x_4144_);
return v___x_4147_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__9(void){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4148_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__8, &l_Lean_Parser_Tactic_mvcgen___closed__8_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__8);
v___x_4149_ = l_Lean_Parser_Tactic_simpStar;
v___x_4150_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4151_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v___x_4149_);
lean_ctor_set(v___x_4151_, 2, v___x_4148_);
return v___x_4151_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__10(void){
_start:
{
uint8_t v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4152_ = 1;
v___x_4153_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__5));
v___x_4154_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_4155_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__9, &l_Lean_Parser_Tactic_mvcgen___closed__9_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__9);
v___x_4156_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4154_);
lean_ctor_set(v___x_4156_, 2, v___x_4153_);
lean_ctor_set_uint8(v___x_4156_, sizeof(void*)*3, v___x_4152_);
return v___x_4156_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__11(void){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4157_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__10, &l_Lean_Parser_Tactic_mvcgen___closed__10_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__10);
v___x_4158_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__7));
v___x_4159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v___x_4157_);
return v___x_4159_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__12(void){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4160_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__11, &l_Lean_Parser_Tactic_mvcgen___closed__11_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__11);
v___x_4161_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__5));
v___x_4162_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4163_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set(v___x_4163_, 1, v___x_4161_);
lean_ctor_set(v___x_4163_, 2, v___x_4160_);
return v___x_4163_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__15(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4167_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__14));
v___x_4168_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__12, &l_Lean_Parser_Tactic_mvcgen___closed__12_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__12);
v___x_4169_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4170_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
lean_ctor_set(v___x_4170_, 1, v___x_4168_);
lean_ctor_set(v___x_4170_, 2, v___x_4167_);
return v___x_4170_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__16(void){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4171_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__15, &l_Lean_Parser_Tactic_mvcgen___closed__15_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__15);
v___x_4172_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4172_);
lean_ctor_set(v___x_4173_, 1, v___x_4171_);
return v___x_4173_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__17(void){
_start:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4174_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__16, &l_Lean_Parser_Tactic_mvcgen___closed__16_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__16);
v___x_4175_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__3, &l_Lean_Parser_Tactic_mvcgen___closed__3_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__3);
v___x_4176_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4177_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___x_4175_);
lean_ctor_set(v___x_4177_, 2, v___x_4174_);
return v___x_4177_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__18(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = l_Lean_Parser_Tactic_invariantAlts;
v___x_4179_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4178_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__19(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4181_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__18, &l_Lean_Parser_Tactic_mvcgen___closed__18_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__18);
v___x_4182_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__17, &l_Lean_Parser_Tactic_mvcgen___closed__17_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__17);
v___x_4183_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4184_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
lean_ctor_set(v___x_4184_, 1, v___x_4182_);
lean_ctor_set(v___x_4184_, 2, v___x_4181_);
return v___x_4184_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__20(void){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4185_ = l_Lean_Parser_Tactic_vcAlts;
v___x_4186_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
lean_ctor_set(v___x_4187_, 1, v___x_4185_);
return v___x_4187_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__21(void){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4188_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__20, &l_Lean_Parser_Tactic_mvcgen___closed__20_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__20);
v___x_4189_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__19, &l_Lean_Parser_Tactic_mvcgen___closed__19_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__19);
v___x_4190_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4191_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v___x_4189_);
lean_ctor_set(v___x_4191_, 2, v___x_4188_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__22(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4192_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__21, &l_Lean_Parser_Tactic_mvcgen___closed__21_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__21);
v___x_4193_ = lean_unsigned_to_nat(1022u);
v___x_4194_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__1));
v___x_4195_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4193_);
lean_ctor_set(v___x_4195_, 2, v___x_4192_);
return v___x_4195_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen(void){
_start:
{
lean_object* v___x_4196_; 
v___x_4196_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__22, &l_Lean_Parser_Tactic_mvcgen___closed__22_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__22);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4207_ = l_Lean_Parser_Tactic_optConfig;
v___x_4208_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__3));
v___x_4209_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4210_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
lean_ctor_set(v___x_4210_, 1, v___x_4208_);
lean_ctor_set(v___x_4210_, 2, v___x_4207_);
return v___x_4210_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5(void){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4211_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__16, &l_Lean_Parser_Tactic_mvcgen___closed__16_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__16);
v___x_4212_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__4, &l_Lean_Parser_Tactic_mvcgenHint___closed__4_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4);
v___x_4213_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4214_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
lean_ctor_set(v___x_4214_, 1, v___x_4212_);
lean_ctor_set(v___x_4214_, 2, v___x_4211_);
return v___x_4214_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6(void){
_start:
{
lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4215_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__5, &l_Lean_Parser_Tactic_mvcgenHint___closed__5_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5);
v___x_4216_ = lean_unsigned_to_nat(1022u);
v___x_4217_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__1));
v___x_4218_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
lean_ctor_set(v___x_4218_, 1, v___x_4216_);
lean_ctor_set(v___x_4218_, 2, v___x_4215_);
return v___x_4218_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint(void){
_start:
{
lean_object* v___x_4219_; 
v___x_4219_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__6, &l_Lean_Parser_Tactic_mvcgenHint___closed__6_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6);
return v___x_4219_;
}
}
lean_object* runtime_initialize_Std_Do(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_GetLit(builtin);
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
l_Lean_Parser_Tactic_invariantDotAlt = _init_l_Lean_Parser_Tactic_invariantDotAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantDotAlt);
l_Lean_Parser_Tactic_invariantCaseAlt = _init_l_Lean_Parser_Tactic_invariantCaseAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantCaseAlt);
l_Lean_Parser_Tactic_invariantAlts = _init_l_Lean_Parser_Tactic_invariantAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantAlts);
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
lean_object* initialize_Std_Tactic_Do_ProofMode(uint8_t builtin);
lean_object* initialize_Init_Data_Array_GetLit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_Do_ProofMode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_GetLit(builtin);
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
