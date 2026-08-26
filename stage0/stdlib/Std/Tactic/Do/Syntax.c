// Lean compiler output
// Module: Std.Tactic.Do.Syntax
// Imports: public import Std.Do public import Std.Tactic.Do.ProofMode public import Init.Data.Array.GetLit public import Init.Grind.Interactive
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
extern lean_object* l_Lean_Parser_Tactic_simpLemma;
extern lean_object* l_Lean_Parser_Tactic_simpErase;
extern lean_object* l_Lean_Parser_Tactic_simpStar;
extern lean_object* l_Lean_Parser_Tactic_optConfig;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
static const lean_string_object l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mclearError__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`mclear` expects an identifier"};
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
static const lean_string_object l_Lean_Parser_Tactic_frameAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "frameAlt"};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 201, 239, 176, 247, 171, 168)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_frameAlt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_invariantCaseAlt___closed__4_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_frameAlt___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_frameAlt___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__4;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__5;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__6;
static lean_once_cell_t l_Lean_Parser_Tactic_frameAlt___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_frameAlt___closed__7;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_frameAlt;
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
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "vcgenDischarge"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 220, 68, 107, 35, 129, 181, 68)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(80, 250, 109, 29, 148, 28, 116, 141)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "`(vcgenDischarge| "};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__2_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 220, 68, 107, 35, 129, 181, 68)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcasesPat_quot___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__8_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischarge_quot = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_vcgenDischarge;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 199, 17, 154, 227, 108, 8, 170)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__4_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischargeGrind = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeGrind___closed__5_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "vcgenDischargeTactic"};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 78, 68, 156, 106, 197, 226, 93)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Tactic_vcAlts___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Tactic_vcgenDischargeTactic = (const lean_object*)&l_Lean_Parser_Tactic_vcgenDischargeTactic___closed__2_value;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 196, 10, 243, 239, 189, 222, 13)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__2 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__2_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__3;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__4;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " until "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__5 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__6 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__6_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mexact___closed__6_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__7 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__7_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__8 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__8_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__9;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " frames "};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__10 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__10_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__11 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__11_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__12;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__13;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__14;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__15;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__16;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__17;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__18;
static const lean_string_object l_Lean_Parser_Tactic_vcgen___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " simplifying_assumptions"};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__19 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__19_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__20 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mrenameI___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__21 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__21_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__22 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__20_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__22_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__23 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 10}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mclear___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__3_value),((lean_object*)&l_Lean_Parser_Tactic_mexists___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__24 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_mvcgen___closed__5_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__24_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__25 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__26 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__25_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__26_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__27 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__27_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__28 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__28_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__23_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__28_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__29 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__29_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__29_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__30 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__30_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__31;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_mcases___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__32 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__32_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__6_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__32_value),((lean_object*)&l_Lean_Parser_Tactic_vcgenDischarge_quot___closed__5_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__33 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__33_value;
static const lean_ctor_object l_Lean_Parser_Tactic_vcgen___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Attr_spec___closed__9_value),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__33_value)}};
static const lean_object* l_Lean_Parser_Tactic_vcgen___closed__34 = (const lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__34_value;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__35;
static lean_once_cell_t l_Lean_Parser_Tactic_vcgen___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_vcgen___closed__36;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_vcgen;
static const lean_string_object l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_Attr_spec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_Attr_spec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_Tactic_massumption___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value_aux_3),((lean_object*)&l_Lean_Parser_Tactic_vcgen___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 229, 87, 15, 155, 212, 124, 96)}};
static const lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Grind_vcgen___closed__1_value;
static lean_once_cell_t l_Lean_Parser_Tactic_Grind_vcgen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Grind_vcgen___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Grind_vcgen;
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
v___x_945_ = l_Lean_mkIdent(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__28));
v___x_953_ = l_Lean_mkIdent(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__32(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__31));
v___x_961_ = l_Lean_mkIdent(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__35(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__34));
v___x_969_ = l_Lean_mkIdent(v___x_968_);
return v___x_969_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__38(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__37));
v___x_977_ = l_Lean_mkIdent(v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__41(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__40));
v___x_985_ = l_Lean_mkIdent(v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__44(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__43));
v___x_993_ = l_Lean_mkIdent(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__47(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__46));
v___x_1001_ = l_Lean_mkIdent(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__50(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__49));
v___x_1009_ = l_Lean_mkIdent(v___x_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__53(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__52));
v___x_1017_ = l_Lean_mkIdent(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__56(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__55));
v___x_1025_ = l_Lean_mkIdent(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__59(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__58));
v___x_1033_ = l_Lean_mkIdent(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__62(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__61));
v___x_1041_ = l_Lean_mkIdent(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__65(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__64));
v___x_1049_ = l_Lean_mkIdent(v___x_1048_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__68(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__67));
v___x_1057_ = l_Lean_mkIdent(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__71(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__70));
v___x_1065_ = l_Lean_mkIdent(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__74(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__73));
v___x_1073_ = l_Lean_mkIdent(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__77(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__76));
v___x_1081_ = l_Lean_mkIdent(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__80(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__79));
v___x_1089_ = l_Lean_mkIdent(v___x_1088_);
return v___x_1089_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__83(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__82));
v___x_1097_ = l_Lean_mkIdent(v___x_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__86(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__85));
v___x_1105_ = l_Lean_mkIdent(v___x_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__89(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__88));
v___x_1113_ = l_Lean_mkIdent(v___x_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__93(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__92));
v___x_1122_ = l_Lean_mkIdent(v___x_1121_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__96(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__95));
v___x_1130_ = l_Lean_mkIdent(v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__99(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__98));
v___x_1138_ = l_Lean_mkIdent(v___x_1137_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__102(void){
_start:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__101));
v___x_1146_ = l_Lean_mkIdent(v___x_1145_);
return v___x_1146_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__105(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__104));
v___x_1154_ = l_Lean_mkIdent(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__108(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__107));
v___x_1162_ = l_Lean_mkIdent(v___x_1161_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__113(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__112));
v___x_1173_ = l_Lean_mkIdent(v___x_1172_);
return v___x_1173_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__116(void){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__115));
v___x_1181_ = l_Lean_mkIdent(v___x_1180_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__119(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__118));
v___x_1189_ = l_Lean_mkIdent(v___x_1188_);
return v___x_1189_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__123(void){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1195_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__122));
v___x_1196_ = l_Lean_mkIdent(v___x_1195_);
return v___x_1196_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__126(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__125));
v___x_1202_ = l_Lean_mkIdent(v___x_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__131(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__130));
v___x_1211_ = l_Lean_mkIdent(v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__134(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__133));
v___x_1218_ = l_Lean_mkIdent(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__137(void){
_start:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1224_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__136));
v___x_1225_ = l_Lean_mkIdent(v___x_1224_);
return v___x_1225_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__140(void){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__139));
v___x_1232_ = l_Lean_mkIdent(v___x_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__143(void){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__142));
v___x_1237_ = l_Lean_mkIdent(v___x_1236_);
return v___x_1237_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__146(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__145));
v___x_1242_ = l_Lean_mkIdent(v___x_1241_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__149(void){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__148));
v___x_1247_ = l_Lean_mkIdent(v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__152(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__151));
v___x_1252_ = l_Lean_mkIdent(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__155(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__154));
v___x_1257_ = l_Lean_mkIdent(v___x_1256_);
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
lean_dec_ref_known(v_x_1895_, 2);
v___x_1900_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0_spec__0___lam__0(v_head_1899_);
return v___x_1900_;
}
else
{
lean_object* v_head_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
lean_inc(v_tail_1898_);
v_head_1901_ = lean_ctor_get(v_x_1895_, 0);
lean_inc(v_head_1901_);
lean_dec_ref_known(v_x_1895_, 2);
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
lean_dec_ref_known(v_x_1942_, 1);
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
lean_dec_ref_known(v_x_1942_, 1);
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
lean_dec_ref_known(v_x_1942_, 1);
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
lean_dec_ref_known(v_x_1942_, 1);
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
lean_dec_ref_known(v_x_1942_, 1);
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
uint8_t v___x_946__boxed_2087_; uint8_t v___x_947__boxed_2088_; size_t v_i_boxed_2089_; size_t v_stop_boxed_2090_; lean_object* v_res_2091_; 
v___x_946__boxed_2087_ = lean_unbox(v___x_2081_);
v___x_947__boxed_2088_ = lean_unbox(v___x_2082_);
v_i_boxed_2089_ = lean_unbox_usize(v_i_2084_);
lean_dec(v_i_2084_);
v_stop_boxed_2090_ = lean_unbox_usize(v_stop_2085_);
lean_dec(v_stop_2085_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_946__boxed_2087_, v___x_947__boxed_2088_, v_as_2083_, v_i_boxed_2089_, v_stop_boxed_2090_, v_b_2086_);
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
lean_object* v___x_2176_; lean_object* v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; lean_object* v_snd_2181_; 
v___x_2176_ = lean_box(v___x_2175_);
v___x_2177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2173_);
v___x_2178_ = ((size_t)0ULL);
v___x_2179_ = lean_usize_of_nat(v___x_2174_);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2150_, v___x_2148_, v___x_2171_, v___x_2178_, v___x_2179_, v___x_2177_);
lean_dec_ref(v___x_2171_);
v_snd_2181_ = lean_ctor_get(v___x_2180_, 1);
lean_inc(v_snd_2181_);
lean_dec_ref(v___x_2180_);
v___y_2120_ = v_snd_2181_;
goto v___jp_2119_;
}
}
}
else
{
lean_object* v___x_2182_; 
lean_dec(v_a_2118_);
v___x_2182_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__1));
return v___x_2182_;
}
}
else
{
lean_object* v___x_2183_; lean_object* v_name_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v_name_2184_ = l_Lean_Syntax_getArg(v_a_2118_, v___x_2183_);
lean_dec(v_a_2118_);
v___x_2185_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2184_);
v___x_2186_ = l_Lean_Syntax_isOfKind(v_name_2184_, v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_name_2184_);
v___x_2187_ = lean_box(0);
return v___x_2187_;
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_name_2184_);
v___x_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(size_t v_sz_2190_, size_t v_i_2191_, lean_object* v_bs_2192_){
_start:
{
uint8_t v___x_2193_; 
v___x_2193_ = lean_usize_dec_lt(v_i_2191_, v_sz_2190_);
if (v___x_2193_ == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v_bs_2192_);
return v___x_2194_;
}
else
{
lean_object* v_v_2195_; lean_object* v___x_2196_; 
v_v_2195_ = lean_array_uget_borrowed(v_bs_2192_, v_i_2191_);
lean_inc(v_v_2195_);
v___x_2196_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_v_2195_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v___x_2197_; 
lean_dec_ref(v_bs_2192_);
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
else
{
lean_object* v_val_2198_; lean_object* v___x_2199_; lean_object* v_bs_x27_2200_; size_t v___x_2201_; size_t v___x_2202_; lean_object* v___x_2203_; 
v_val_2198_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_val_2198_);
lean_dec_ref_known(v___x_2196_, 1);
v___x_2199_ = lean_unsigned_to_nat(0u);
v_bs_x27_2200_ = lean_array_uset(v_bs_2192_, v_i_2191_, v___x_2199_);
v___x_2201_ = ((size_t)1ULL);
v___x_2202_ = lean_usize_add(v_i_2191_, v___x_2201_);
v___x_2203_ = lean_array_uset(v_bs_x27_2200_, v_i_2191_, v_val_2198_);
v_i_2191_ = v___x_2202_;
v_bs_2192_ = v___x_2203_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(lean_object* v_a_2205_){
_start:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2206_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__1));
lean_inc(v_a_2205_);
v___x_2207_ = l_Lean_Syntax_isOfKind(v_a_2205_, v___x_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec(v_a_2205_);
v___x_2208_ = lean_box(0);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_args_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2209_ = lean_unsigned_to_nat(0u);
v___x_2210_ = l_Lean_Syntax_getArg(v_a_2205_, v___x_2209_);
lean_dec(v_a_2205_);
v_args_2211_ = l_Lean_Syntax_getArgs(v___x_2210_);
lean_dec(v___x_2210_);
v___x_2212_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_args_2211_);
lean_dec_ref(v_args_2211_);
v___x_2213_ = lean_array_get_size(v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(1u);
v___x_2215_ = lean_nat_dec_eq(v___x_2213_, v___x_2214_);
if (v___x_2215_ == 0)
{
size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
v_sz_2216_ = lean_array_size(v___x_2212_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_2216_, v___x_2217_, v___x_2212_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_box(0);
return v___x_2219_;
}
else
{
lean_object* v_val_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2229_; 
v_val_2220_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2222_ = v___x_2218_;
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_val_2220_);
lean_dec(v___x_2218_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2229_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_array_to_list(v_val_2220_);
v___x_2225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2225_);
v___x_2227_ = v___x_2222_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_array_fget(v___x_2212_, v___x_2209_);
lean_dec_ref(v___x_2212_);
v___x_2231_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v___x_2230_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(size_t v_sz_2232_, size_t v_i_2233_, lean_object* v_bs_2234_){
_start:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_usize_dec_lt(v_i_2233_, v_sz_2232_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_bs_2234_);
return v___x_2236_;
}
else
{
lean_object* v_v_2237_; lean_object* v___x_2238_; 
v_v_2237_ = lean_array_uget_borrowed(v_bs_2234_, v_i_2233_);
lean_inc(v_v_2237_);
v___x_2238_ = l_Lean_Parser_Tactic_MCasesPat_parse_goAlts(v_v_2237_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v___x_2239_; 
lean_dec_ref(v_bs_2234_);
v___x_2239_ = lean_box(0);
return v___x_2239_;
}
else
{
lean_object* v_val_2240_; lean_object* v___x_2241_; lean_object* v_bs_x27_2242_; size_t v___x_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
v_val_2240_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_val_2240_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2241_ = lean_unsigned_to_nat(0u);
v_bs_x27_2242_ = lean_array_uset(v_bs_2234_, v_i_2233_, v___x_2241_);
v___x_2243_ = ((size_t)1ULL);
v___x_2244_ = lean_usize_add(v_i_2233_, v___x_2243_);
v___x_2245_ = lean_array_uset(v_bs_x27_2242_, v_i_2233_, v_val_2240_);
v_i_2233_ = v___x_2244_;
v_bs_2234_ = v___x_2245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1___boxed(lean_object* v_sz_2247_, lean_object* v_i_2248_, lean_object* v_bs_2249_){
_start:
{
size_t v_sz_boxed_2250_; size_t v_i_boxed_2251_; lean_object* v_res_2252_; 
v_sz_boxed_2250_ = lean_unbox_usize(v_sz_2247_);
lean_dec(v_sz_2247_);
v_i_boxed_2251_ = lean_unbox_usize(v_i_2248_);
lean_dec(v_i_2248_);
v_res_2252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__1(v_sz_boxed_2250_, v_i_boxed_2251_, v_bs_2249_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4___boxed(lean_object* v_sz_2253_, lean_object* v_i_2254_, lean_object* v_bs_2255_){
_start:
{
size_t v_sz_boxed_2256_; size_t v_i_boxed_2257_; lean_object* v_res_2258_; 
v_sz_boxed_2256_ = lean_unbox_usize(v_sz_2253_);
lean_dec(v_sz_2253_);
v_i_boxed_2257_ = lean_unbox_usize(v_i_2254_);
lean_dec(v_i_2254_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MCasesPat_parse_goAlts_spec__4(v_sz_boxed_2256_, v_i_boxed_2257_, v_bs_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(lean_object* v_k_2265_){
_start:
{
lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___closed__1));
v___x_2267_ = lean_name_eq(v_k_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
uint8_t v___x_2268_; 
v___x_2268_ = 1;
return v___x_2268_;
}
else
{
uint8_t v___x_2269_; 
v___x_2269_ = 0;
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___lam__0___boxed(lean_object* v_k_2270_){
_start:
{
uint8_t v_res_2271_; lean_object* v_r_2272_; 
v_res_2271_ = l_Lean_Parser_Tactic_MCasesPat_parse___lam__0(v_k_2270_);
lean_dec(v_k_2270_);
v_r_2272_ = lean_box(v_res_2271_);
return v_r_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse(lean_object* v_pat_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_){
_start:
{
lean_object* v___f_2277_; lean_object* v___x_2278_; 
v___f_2277_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2275_);
v___x_2278_ = l_Lean_expandMacros(v_pat_2274_, v___f_2277_, v_a_2275_, v_a_2276_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v_a_2280_ = lean_ctor_get(v___x_2278_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2282_ = v___x_2278_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_inc(v_a_2279_);
lean_dec(v___x_2278_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_Parser_Tactic_MCasesPat_parse_go(v_a_2279_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
lean_del_object(v___x_2282_);
v___x_2285_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2280_);
return v___x_2285_;
}
else
{
lean_object* v_val_2286_; lean_object* v___x_2288_; 
v_val_2286_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_val_2286_);
lean_dec_ref_known(v___x_2284_, 1);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v_val_2286_);
v___x_2288_ = v___x_2282_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_val_2286_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_a_2280_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
v_a_2291_ = lean_ctor_get(v___x_2278_, 0);
v_a_2292_ = lean_ctor_get(v___x_2278_, 1);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2278_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_inc(v_a_2291_);
lean_dec(v___x_2278_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2291_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MCasesPat_parse___boxed(lean_object* v_pat_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_Parser_Tactic_MCasesPat_parse(v_pat_2300_, v_a_2301_, v_a_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(lean_object* v_x_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2348_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesError___closed__1));
v___x_2349_ = l_Lean_Syntax_isOfKind(v_x_2345_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___x_2350_ = lean_box(1);
v___x_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_a_2347_);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___closed__0));
v___x_2353_ = l_Lean_Macro_throwError___redArg(v___x_2352_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_a_2355_ = lean_ctor_get(v___x_2353_, 1);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2353_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2354_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2363_ = lean_ctor_get(v___x_2353_, 0);
v_a_2364_ = lean_ctor_get(v___x_2353_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2353_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_inc(v_a_2363_);
lean_dec(v___x_2353_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2363_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1___boxed(lean_object* v_x_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mcasesError__1(v_x_2372_, v_a_2373_, v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrefinePat(void){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_box(0);
return v___x_2405_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2412_ = l_Lean_binderIdent;
v___x_2413_ = lean_unsigned_to_nat(1022u);
v___x_2414_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
v___x_2415_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2414_);
lean_ctor_set(v___x_2415_, 1, v___x_2413_);
lean_ctor_set(v___x_2415_, 2, v___x_2412_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat__(void){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat___00__closed__2);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__4);
v___x_2497_ = lean_unsigned_to_nat(1022u);
v___x_2498_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2499_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v___x_2497_);
lean_ctor_set(v___x_2499_, 2, v___x_2496_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_u25a1__(void){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__2);
return v___x_2500_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2510_ = l_Lean_binderIdent;
v___x_2511_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__3));
v___x_2512_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_2513_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
lean_ctor_set(v___x_2513_, 1, v___x_2511_);
lean_ctor_set(v___x_2513_, 2, v___x_2510_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2514_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__4);
v___x_2515_ = lean_unsigned_to_nat(1022u);
v___x_2516_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
v___x_2517_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
lean_ctor_set(v___x_2517_, 1, v___x_2515_);
lean_ctor_set(v___x_2517_, 2, v___x_2514_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x3f__(void){
_start:
{
lean_object* v___x_2518_; 
v___x_2518_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5, &l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5_once, _init_l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__5);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(lean_object* v_x_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x25___00__closed__1));
lean_inc(v_x_2534_);
v___x_2538_ = l_Lean_Syntax_isOfKind(v_x_2534_, v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_x_2534_);
v___x_2539_ = lean_box(1);
v___x_2540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
lean_ctor_set(v___x_2540_, 1, v_a_2536_);
return v___x_2540_;
}
else
{
lean_object* v_ref_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v_ref_2541_ = lean_ctor_get(v_a_2535_, 5);
v___x_2542_ = lean_unsigned_to_nat(1u);
v___x_2543_ = l_Lean_Syntax_getArg(v_x_2534_, v___x_2542_);
lean_dec(v_x_2534_);
v___x_2544_ = 0;
v___x_2545_ = l_Lean_SourceInfo_fromRef(v_ref_2541_, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
v___x_2547_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__2));
lean_inc_n(v___x_2545_, 2);
v___x_2548_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2545_);
lean_ctor_set(v___x_2548_, 1, v___x_2547_);
v___x_2549_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u231c___u231d___closed__5));
v___x_2550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2545_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node3(v___x_2545_, v___x_2546_, v___x_2548_, v___x_2543_, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
lean_ctor_set(v___x_2552_, 1, v_a_2536_);
return v___x_2552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1___boxed(lean_object* v_x_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x25____1(v_x_2553_, v_a_2554_, v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2556_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2563_ = lean_obj_once(&l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4, &l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4_once, _init_l_Lean_Parser_Tactic_mcasesPat_x23___00__closed__4);
v___x_2564_ = lean_unsigned_to_nat(1022u);
v___x_2565_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
v___x_2566_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2565_);
lean_ctor_set(v___x_2566_, 1, v___x_2564_);
lean_ctor_set(v___x_2566_, 2, v___x_2563_);
return v___x_2566_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mrefinePat_x23__(void){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_obj_once(&l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2, &l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2_once, _init_l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__2);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(lean_object* v_x_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x23___00__closed__1));
lean_inc(v_x_2568_);
v___x_2572_ = l_Lean_Syntax_isOfKind(v_x_2568_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec(v_x_2568_);
v___x_2573_ = lean_box(1);
v___x_2574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
lean_ctor_set(v___x_2574_, 1, v_a_2570_);
return v___x_2574_;
}
else
{
lean_object* v_ref_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_ref_2575_ = lean_ctor_get(v_a_2569_, 5);
v___x_2576_ = lean_unsigned_to_nat(1u);
v___x_2577_ = l_Lean_Syntax_getArg(v_x_2568_, v___x_2576_);
lean_dec(v_x_2568_);
v___x_2578_ = 0;
v___x_2579_ = l_Lean_SourceInfo_fromRef(v_ref_2575_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
v___x_2581_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat_u25a1___00__closed__2));
lean_inc(v___x_2579_);
v___x_2582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2579_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = l_Lean_Syntax_node2(v___x_2579_, v___x_2580_, v___x_2582_, v___x_2577_);
v___x_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
lean_ctor_set(v___x_2584_, 1, v_a_2570_);
return v___x_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1___boxed(lean_object* v_x_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefinePat_x23____1(v_x_2585_, v_a_2586_, v_a_2587_);
lean_dec_ref(v_a_2586_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx(lean_object* v_x_2589_){
_start:
{
switch(lean_obj_tag(v_x_2589_))
{
case 0:
{
lean_object* v___x_2590_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
return v___x_2590_;
}
case 1:
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_unsigned_to_nat(1u);
return v___x_2591_;
}
case 2:
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_unsigned_to_nat(2u);
return v___x_2592_;
}
case 3:
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_unsigned_to_nat(3u);
return v___x_2593_;
}
default: 
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_unsigned_to_nat(4u);
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorIdx___boxed(lean_object* v_x_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Parser_Tactic_MRefinePat_ctorIdx(v_x_2595_);
lean_dec_ref(v_x_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(lean_object* v_t_2597_, lean_object* v_k_2598_){
_start:
{
lean_object* v_name_2599_; lean_object* v___x_2600_; 
v_name_2599_ = lean_ctor_get(v_t_2597_, 0);
lean_inc(v_name_2599_);
lean_dec_ref(v_t_2597_);
v___x_2600_ = lean_apply_1(v_k_2598_, v_name_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim(lean_object* v_motive__1_2601_, lean_object* v_ctorIdx_2602_, lean_object* v_t_2603_, lean_object* v_h_2604_, lean_object* v_k_2605_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2603_, v_k_2605_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_ctorElim___boxed(lean_object* v_motive__1_2607_, lean_object* v_ctorIdx_2608_, lean_object* v_t_2609_, lean_object* v_h_2610_, lean_object* v_k_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim(v_motive__1_2607_, v_ctorIdx_2608_, v_t_2609_, v_h_2610_, v_k_2611_);
lean_dec(v_ctorIdx_2608_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim___redArg(lean_object* v_t_2613_, lean_object* v_one_2614_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2613_, v_one_2614_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_one_elim(lean_object* v_motive__1_2616_, lean_object* v_t_2617_, lean_object* v_h_2618_, lean_object* v_one_2619_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2617_, v_one_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim___redArg(lean_object* v_t_2621_, lean_object* v_tuple_2622_){
_start:
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2621_, v_tuple_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_tuple_elim(lean_object* v_motive__1_2624_, lean_object* v_t_2625_, lean_object* v_h_2626_, lean_object* v_tuple_2627_){
_start:
{
lean_object* v___x_2628_; 
v___x_2628_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2625_, v_tuple_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim___redArg(lean_object* v_t_2629_, lean_object* v_pure_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2629_, v_pure_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_pure_elim(lean_object* v_motive__1_2632_, lean_object* v_t_2633_, lean_object* v_h_2634_, lean_object* v_pure_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2633_, v_pure_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim___redArg(lean_object* v_t_2637_, lean_object* v_stateful_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2637_, v_stateful_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_stateful_elim(lean_object* v_motive__1_2640_, lean_object* v_t_2641_, lean_object* v_h_2642_, lean_object* v_stateful_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2641_, v_stateful_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim___redArg(lean_object* v_t_2645_, lean_object* v_hole_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2645_, v_hole_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_hole_elim(lean_object* v_motive__1_2648_, lean_object* v_t_2649_, lean_object* v_h_2650_, lean_object* v_hole_2651_){
_start:
{
lean_object* v___x_2652_; 
v___x_2652_ = l_Lean_Parser_Tactic_MRefinePat_ctorElim___redArg(v_t_2649_, v_hole_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
if (lean_obj_tag(v_x_2667_) == 0)
{
lean_dec(v_x_2665_);
return v_x_2666_;
}
else
{
lean_object* v_head_2668_; lean_object* v_tail_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2680_; 
v_head_2668_ = lean_ctor_get(v_x_2667_, 0);
v_tail_2669_ = lean_ctor_get(v_x_2667_, 1);
v_isSharedCheck_2680_ = !lean_is_exclusive(v_x_2667_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2671_ = v_x_2667_;
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_tail_2669_);
lean_inc(v_head_2668_);
lean_dec(v_x_2667_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2680_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
lean_inc(v_x_2665_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 5);
lean_ctor_set(v___x_2671_, 1, v_x_2665_);
lean_ctor_set(v___x_2671_, 0, v_x_2666_);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_x_2666_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_x_2665_);
v___x_2674_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2675_ = lean_unsigned_to_nat(0u);
v___x_2676_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2668_, v___x_2675_);
v___x_2677_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2674_);
lean_ctor_set(v___x_2677_, 1, v___x_2676_);
v_x_2666_ = v___x_2677_;
v_x_2667_ = v_tail_2669_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(lean_object* v_x_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_dec(v_x_2681_);
return v_x_2682_;
}
else
{
lean_object* v_head_2684_; lean_object* v_tail_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2696_; 
v_head_2684_ = lean_ctor_get(v_x_2683_, 0);
v_tail_2685_ = lean_ctor_get(v_x_2683_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_x_2683_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2687_ = v_x_2683_;
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_tail_2685_);
lean_inc(v_head_2684_);
lean_dec(v_x_2683_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
lean_inc(v_x_2681_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 5);
lean_ctor_set(v___x_2687_, 1, v_x_2681_);
lean_ctor_set(v___x_2687_, 0, v_x_2682_);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_x_2682_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v_x_2681_);
v___x_2690_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2691_ = lean_unsigned_to_nat(0u);
v___x_2692_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_head_2684_, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2690_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1_spec__2(v_x_2681_, v___x_2693_, v_tail_2685_);
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(lean_object* v_x_2697_, lean_object* v_x_2698_){
_start:
{
if (lean_obj_tag(v_x_2697_) == 0)
{
lean_object* v___x_2699_; 
lean_dec(v_x_2698_);
v___x_2699_ = lean_box(0);
return v___x_2699_;
}
else
{
lean_object* v_tail_2700_; 
v_tail_2700_ = lean_ctor_get(v_x_2697_, 1);
if (lean_obj_tag(v_tail_2700_) == 0)
{
lean_object* v_head_2701_; lean_object* v___x_2702_; 
lean_dec(v_x_2698_);
v_head_2701_ = lean_ctor_get(v_x_2697_, 0);
lean_inc(v_head_2701_);
lean_dec_ref_known(v_x_2697_, 2);
v___x_2702_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2701_);
return v___x_2702_;
}
else
{
lean_object* v_head_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
lean_inc(v_tail_2700_);
v_head_2703_ = lean_ctor_get(v_x_2697_, 0);
lean_inc(v_head_2703_);
lean_dec_ref_known(v_x_2697_, 2);
v___x_2704_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(v_head_2703_);
v___x_2705_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0_spec__1(v_x_2698_, v___x_2704_, v_tail_2700_);
return v___x_2705_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(lean_object* v_a_2706_){
_start:
{
if (lean_obj_tag(v_a_2706_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__1));
return v___x_2707_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; 
v___x_2708_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__3));
v___x_2709_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0(v_a_2706_, v___x_2708_);
v___x_2710_ = lean_obj_once(&l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__5);
v___x_2711_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__6));
v___x_2712_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___x_2709_);
v___x_2713_ = ((lean_object*)(l_List_repr___at___00Lean_Parser_Tactic_instReprMCasesPat_repr_spec__0___redArg___closed__7));
v___x_2714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2712_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2710_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = 0;
v___x_2717_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set_uint8(v___x_2717_, sizeof(void*)*1, v___x_2716_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr(lean_object* v_x_2736_, lean_object* v_prec_2737_){
_start:
{
switch(lean_obj_tag(v_x_2736_))
{
case 0:
{
lean_object* v_name_2738_; lean_object* v___y_2740_; lean_object* v___x_2748_; uint8_t v___x_2749_; 
v_name_2738_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_name_2738_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2748_ = lean_unsigned_to_nat(1024u);
v___x_2749_ = lean_nat_dec_le(v___x_2748_, v_prec_2737_);
if (v___x_2749_ == 0)
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2740_ = v___x_2750_;
goto v___jp_2739_;
}
else
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2740_ = v___x_2751_;
goto v___jp_2739_;
}
v___jp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2741_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__2));
v___x_2742_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2738_);
v___x_2743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2741_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
lean_inc(v___y_2740_);
v___x_2744_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___y_2740_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = 0;
v___x_2746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set_uint8(v___x_2746_, sizeof(void*)*1, v___x_2745_);
v___x_2747_ = l_Repr_addAppParen(v___x_2746_, v_prec_2737_);
return v___x_2747_;
}
}
case 1:
{
lean_object* v_args_2752_; lean_object* v___y_2754_; lean_object* v___x_2762_; uint8_t v___x_2763_; 
v_args_2752_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_args_2752_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2762_ = lean_unsigned_to_nat(1024u);
v___x_2763_ = lean_nat_dec_le(v___x_2762_, v_prec_2737_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; 
v___x_2764_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2754_ = v___x_2764_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2754_ = v___x_2765_;
goto v___jp_2753_;
}
v___jp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2755_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__5));
v___x_2756_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_args_2752_);
v___x_2757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
lean_inc(v___y_2754_);
v___x_2758_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___y_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = 0;
v___x_2760_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set_uint8(v___x_2760_, sizeof(void*)*1, v___x_2759_);
v___x_2761_ = l_Repr_addAppParen(v___x_2760_, v_prec_2737_);
return v___x_2761_;
}
}
case 2:
{
lean_object* v_h_2766_; lean_object* v___y_2768_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v_h_2766_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_h_2766_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2776_ = lean_unsigned_to_nat(1024u);
v___x_2777_ = lean_nat_dec_le(v___x_2776_, v_prec_2737_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2768_ = v___x_2778_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2768_ = v___x_2779_;
goto v___jp_2767_;
}
v___jp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2769_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__8));
v___x_2770_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2766_);
v___x_2771_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
lean_inc(v___y_2768_);
v___x_2772_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___y_2768_);
lean_ctor_set(v___x_2772_, 1, v___x_2771_);
v___x_2773_ = 0;
v___x_2774_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2774_, 0, v___x_2772_);
lean_ctor_set_uint8(v___x_2774_, sizeof(void*)*1, v___x_2773_);
v___x_2775_ = l_Repr_addAppParen(v___x_2774_, v_prec_2737_);
return v___x_2775_;
}
}
case 3:
{
lean_object* v_h_2780_; lean_object* v___y_2782_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_h_2780_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_h_2780_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2790_ = lean_unsigned_to_nat(1024u);
v___x_2791_ = lean_nat_dec_le(v___x_2790_, v_prec_2737_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2782_ = v___x_2792_;
goto v___jp_2781_;
}
else
{
lean_object* v___x_2793_; 
v___x_2793_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2782_ = v___x_2793_;
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2783_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__11));
v___x_2784_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_h_2780_);
v___x_2785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2783_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
lean_inc(v___y_2782_);
v___x_2786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___y_2782_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = 0;
v___x_2788_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set_uint8(v___x_2788_, sizeof(void*)*1, v___x_2787_);
v___x_2789_ = l_Repr_addAppParen(v___x_2788_, v_prec_2737_);
return v___x_2789_;
}
}
default: 
{
lean_object* v_name_2794_; lean_object* v___y_2796_; lean_object* v___x_2804_; uint8_t v___x_2805_; 
v_name_2794_ = lean_ctor_get(v_x_2736_, 0);
lean_inc(v_name_2794_);
lean_dec_ref_known(v_x_2736_, 1);
v___x_2804_ = lean_unsigned_to_nat(1024u);
v___x_2805_ = lean_nat_dec_le(v___x_2804_, v_prec_2737_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__5);
v___y_2796_ = v___x_2806_;
goto v___jp_2795_;
}
else
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_obj_once(&l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6, &l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6_once, _init_l_Lean_Parser_Tactic_instReprMCasesPat_repr___closed__6);
v___y_2796_ = v___x_2807_;
goto v___jp_2795_;
}
v___jp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2797_ = ((lean_object*)(l_Lean_Parser_Tactic_instReprMRefinePat_repr___closed__14));
v___x_2798_ = l_Lean_Syntax_instReprTSyntax_repr___redArg(v_name_2794_);
v___x_2799_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2797_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
lean_inc(v___y_2796_);
v___x_2800_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___y_2796_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = 0;
v___x_2802_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set_uint8(v___x_2802_, sizeof(void*)*1, v___x_2801_);
v___x_2803_ = l_Repr_addAppParen(v___x_2802_, v_prec_2737_);
return v___x_2803_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0_spec__0___lam__0(lean_object* v___y_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v___y_2808_, v___x_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_instReprMRefinePat_repr___boxed(lean_object* v_x_2811_, lean_object* v_prec_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_Parser_Tactic_instReprMRefinePat_repr(v_x_2811_, v_prec_2812_);
lean_dec(v_prec_2812_);
return v_res_2813_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(lean_object* v_a_2814_, lean_object* v_n_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___redArg(v_a_2814_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0___boxed(lean_object* v_a_2817_, lean_object* v_n_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_List_repr___at___00Lean_Parser_Tactic_instReprMRefinePat_repr_spec__0(v_a_2817_, v_n_2818_);
lean_dec(v_n_2818_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(size_t v_sz_2826_, size_t v_i_2827_, lean_object* v_bs_2828_){
_start:
{
uint8_t v___x_2829_; 
v___x_2829_ = lean_usize_dec_lt(v_i_2827_, v_sz_2826_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_bs_2828_);
return v___x_2830_;
}
else
{
lean_object* v_v_2831_; lean_object* v___x_2832_; lean_object* v_bs_x27_2833_; size_t v___x_2834_; size_t v___x_2835_; lean_object* v___x_2836_; 
v_v_2831_ = lean_array_uget(v_bs_2828_, v_i_2827_);
v___x_2832_ = lean_unsigned_to_nat(0u);
v_bs_x27_2833_ = lean_array_uset(v_bs_2828_, v_i_2827_, v___x_2832_);
v___x_2834_ = ((size_t)1ULL);
v___x_2835_ = lean_usize_add(v_i_2827_, v___x_2834_);
v___x_2836_ = lean_array_uset(v_bs_x27_2833_, v_i_2827_, v_v_2831_);
v_i_2827_ = v___x_2835_;
v_bs_2828_ = v___x_2836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0___boxed(lean_object* v_sz_2838_, lean_object* v_i_2839_, lean_object* v_bs_2840_){
_start:
{
size_t v_sz_boxed_2841_; size_t v_i_boxed_2842_; lean_object* v_res_2843_; 
v_sz_boxed_2841_ = lean_unbox_usize(v_sz_2838_);
lean_dec(v_sz_2838_);
v_i_boxed_2842_ = lean_unbox_usize(v_i_2839_);
lean_dec(v_i_2839_);
v_res_2843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_boxed_2841_, v_i_boxed_2842_, v_bs_2840_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse_go(lean_object* v_a_2844_){
_start:
{
lean_object* v___y_2846_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat___00__closed__1));
lean_inc(v_a_2844_);
v___x_2872_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2871_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x3f___00__closed__1));
lean_inc(v_a_2844_);
v___x_2874_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2873_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u27e8___u27e9___closed__1));
lean_inc(v_a_2844_);
v___x_2876_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2877_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u231c___u231d___closed__1));
lean_inc(v_a_2844_);
v___x_2878_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_u25a1___00__closed__1));
lean_inc(v_a_2844_);
v___x_2880_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; uint8_t v___x_2882_; 
v___x_2881_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePat_x28___x29___closed__1));
lean_inc(v_a_2844_);
v___x_2882_ = l_Lean_Syntax_isOfKind(v_a_2844_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; 
lean_dec(v_a_2844_);
v___x_2883_ = lean_box(0);
return v___x_2883_;
}
else
{
lean_object* v___x_2884_; lean_object* v_pat_2885_; 
v___x_2884_ = lean_unsigned_to_nat(1u);
v_pat_2885_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2884_);
lean_dec(v_a_2844_);
v_a_2844_ = v_pat_2885_;
goto _start;
}
}
else
{
lean_object* v___x_2887_; lean_object* v_h_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2887_ = lean_unsigned_to_nat(1u);
v_h_2888_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2887_);
lean_dec(v_a_2844_);
v___x_2889_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_h_2888_);
v___x_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
}
else
{
lean_object* v___x_2891_; lean_object* v_h_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2891_ = lean_unsigned_to_nat(1u);
v_h_2892_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2891_);
lean_dec(v_a_2844_);
v___x_2893_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_h_2892_);
v___x_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
return v___x_2894_;
}
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2895_ = lean_unsigned_to_nat(1u);
v___x_2896_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2895_);
lean_dec(v_a_2844_);
v___x_2897_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefinePats___closed__1));
lean_inc(v___x_2896_);
v___x_2898_ = l_Lean_Syntax_isOfKind(v___x_2896_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
return v___x_2899_;
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = l_Lean_Syntax_getArg(v___x_2896_, v___x_2900_);
lean_dec(v___x_2896_);
v___x_2902_ = l_Lean_Syntax_getArgs(v___x_2901_);
lean_dec(v___x_2901_);
v___x_2903_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___x_2904_ = lean_array_get_size(v___x_2902_);
v___x_2905_ = lean_nat_dec_lt(v___x_2900_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_dec_ref(v___x_2902_);
v___y_2846_ = v___x_2903_;
goto v___jp_2845_;
}
else
{
lean_object* v___x_2906_; lean_object* v___x_2907_; size_t v___x_2908_; size_t v___x_2909_; lean_object* v___x_2910_; lean_object* v_snd_2911_; 
v___x_2906_ = lean_box(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v___x_2903_);
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2904_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Parser_Tactic_MCasesPat_parse_go_spec__2(v___x_2898_, v___x_2874_, v___x_2902_, v___x_2908_, v___x_2909_, v___x_2907_);
lean_dec_ref(v___x_2902_);
v_snd_2911_ = lean_ctor_get(v___x_2910_, 1);
lean_inc(v_snd_2911_);
lean_dec_ref(v___x_2910_);
v___y_2846_ = v_snd_2911_;
goto v___jp_2845_;
}
}
}
}
else
{
lean_object* v___x_2912_; lean_object* v_name_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2912_ = lean_unsigned_to_nat(1u);
v_name_2913_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2912_);
lean_dec(v_a_2844_);
v___x_2914_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_name_2913_);
v___x_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
else
{
lean_object* v___x_2916_; lean_object* v_name_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v_name_2917_ = l_Lean_Syntax_getArg(v_a_2844_, v___x_2916_);
lean_dec(v_a_2844_);
v___x_2918_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
lean_inc(v_name_2917_);
v___x_2919_ = l_Lean_Syntax_isOfKind(v_name_2917_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
lean_dec(v_name_2917_);
v___x_2920_ = lean_box(0);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2921_, 0, v_name_2917_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
return v___x_2922_;
}
}
v___jp_2845_:
{
size_t v_sz_2847_; size_t v___x_2848_; lean_object* v___x_2849_; 
v_sz_2847_ = lean_array_size(v___y_2846_);
v___x_2848_ = ((size_t)0ULL);
v___x_2849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__0(v_sz_2847_, v___x_2848_, v___y_2846_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; 
v___x_2850_ = lean_box(0);
return v___x_2850_;
}
else
{
lean_object* v_val_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2870_; 
v_val_2851_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2853_ = v___x_2849_;
v_isShared_2854_ = v_isSharedCheck_2870_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_val_2851_);
lean_dec(v___x_2849_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2870_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
size_t v_sz_2855_; lean_object* v___x_2856_; 
v_sz_2855_ = lean_array_size(v_val_2851_);
v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_2855_, v___x_2848_, v_val_2851_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v___x_2857_; 
lean_del_object(v___x_2853_);
v___x_2857_ = lean_box(0);
return v___x_2857_;
}
else
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2869_; 
v_val_2858_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2860_ = v___x_2856_;
v_isShared_2861_ = v_isSharedCheck_2869_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v___x_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2869_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = lean_array_to_list(v_val_2858_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2862_);
v___x_2864_ = v___x_2853_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2866_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2864_);
v___x_2866_ = v___x_2860_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(size_t v_sz_2923_, size_t v_i_2924_, lean_object* v_bs_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = lean_usize_dec_lt(v_i_2924_, v_sz_2923_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; 
v___x_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2927_, 0, v_bs_2925_);
return v___x_2927_;
}
else
{
lean_object* v_v_2928_; lean_object* v___x_2929_; 
v_v_2928_ = lean_array_uget_borrowed(v_bs_2925_, v_i_2924_);
lean_inc(v_v_2928_);
v___x_2929_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_v_2928_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; 
lean_dec_ref(v_bs_2925_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v_val_2931_; lean_object* v___x_2932_; lean_object* v_bs_x27_2933_; size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v_val_2931_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_val_2931_);
lean_dec_ref_known(v___x_2929_, 1);
v___x_2932_ = lean_unsigned_to_nat(0u);
v_bs_x27_2933_ = lean_array_uset(v_bs_2925_, v_i_2924_, v___x_2932_);
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2924_, v___x_2934_);
v___x_2936_ = lean_array_uset(v_bs_x27_2933_, v_i_2924_, v_val_2931_);
v_i_2924_ = v___x_2935_;
v_bs_2925_ = v___x_2936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1___boxed(lean_object* v_sz_2938_, lean_object* v_i_2939_, lean_object* v_bs_2940_){
_start:
{
size_t v_sz_boxed_2941_; size_t v_i_boxed_2942_; lean_object* v_res_2943_; 
v_sz_boxed_2941_ = lean_unbox_usize(v_sz_2938_);
lean_dec(v_sz_2938_);
v_i_boxed_2942_ = lean_unbox_usize(v_i_2939_);
lean_dec(v_i_2939_);
v_res_2943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Parser_Tactic_MRefinePat_parse_go_spec__1(v_sz_boxed_2941_, v_i_boxed_2942_, v_bs_2940_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse(lean_object* v_pat_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_){
_start:
{
lean_object* v___f_2947_; lean_object* v___x_2948_; 
v___f_2947_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse___closed__0));
lean_inc_ref(v_a_2945_);
v___x_2948_ = l_Lean_expandMacros(v_pat_2944_, v___f_2947_, v_a_2945_, v_a_2946_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2960_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_a_2950_ = lean_ctor_get(v___x_2948_, 1);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2952_ = v___x_2948_;
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2960_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; 
v___x_2954_ = l_Lean_Parser_Tactic_MRefinePat_parse_go(v_a_2949_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; 
lean_del_object(v___x_2952_);
v___x_2955_ = l_Lean_Macro_throwUnsupported___redArg(v_a_2950_);
return v___x_2955_;
}
else
{
lean_object* v_val_2956_; lean_object* v___x_2958_; 
v_val_2956_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v___x_2954_, 1);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v_val_2956_);
v___x_2958_ = v___x_2952_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_val_2956_);
lean_ctor_set(v_reuseFailAlloc_2959_, 1, v_a_2950_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v_a_2961_ = lean_ctor_get(v___x_2948_, 0);
v_a_2962_ = lean_ctor_get(v___x_2948_, 1);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2948_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_inc(v_a_2961_);
lean_dec(v___x_2948_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2961_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_MRefinePat_parse___boxed(lean_object* v_pat_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Parser_Tactic_MRefinePat_parse(v_pat_2970_, v_a_2971_, v_a_2972_);
lean_dec_ref(v_a_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(lean_object* v_x_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_){
_start:
{
lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3007_ = ((lean_object*)(l_Lean_Parser_Tactic_mrefineError___closed__1));
v___x_3008_ = l_Lean_Syntax_isOfKind(v_x_3004_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_box(1);
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_a_3006_);
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___closed__0));
v___x_3012_ = l_Lean_Macro_throwError___redArg(v___x_3011_, v_a_3005_, v_a_3006_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
v_a_3014_ = lean_ctor_get(v___x_3012_, 1);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3012_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_inc(v_a_3013_);
lean_dec(v___x_3012_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_a_3022_ = lean_ctor_get(v___x_3012_, 0);
v_a_3023_ = lean_ctor_get(v___x_3012_, 1);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3012_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_inc(v_a_3022_);
lean_dec(v___x_3012_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3022_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1___boxed(lean_object* v_x_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrefineError__1(v_x_3031_, v_a_3032_, v_a_3033_);
lean_dec_ref(v_a_3032_);
return v_res_3034_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mintroPat(void){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = lean_box(0);
return v___x_3064_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3085_ = l_Lean_binderIdent;
v___x_3086_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__3));
v___x_3087_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3088_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
lean_ctor_set(v___x_3088_, 1, v___x_3086_);
lean_ctor_set(v___x_3088_, 2, v___x_3085_);
return v___x_3088_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5(void){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3089_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__4);
v___x_3090_ = lean_unsigned_to_nat(1022u);
v___x_3091_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__1));
v___x_3092_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
lean_ctor_set(v___x_3092_, 1, v___x_3090_);
lean_ctor_set(v___x_3092_, 2, v___x_3089_);
return v___x_3092_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mintroPat_u2200__(void){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_obj_once(&l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5, &l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5_once, _init_l_Lean_Parser_Tactic_mintroPat_u2200___00__closed__5);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(lean_object* v_x_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_){
_start:
{
lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroError___closed__1));
v___x_3135_ = l_Lean_Syntax_isOfKind(v_x_3131_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3136_ = lean_box(1);
v___x_3137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3137_, 0, v___x_3136_);
lean_ctor_set(v___x_3137_, 1, v_a_3133_);
return v___x_3137_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___closed__0));
v___x_3139_ = l_Lean_Macro_throwError___redArg(v___x_3138_, v_a_3132_, v_a_3133_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_a_3141_ = lean_ctor_get(v___x_3139_, 1);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3139_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3140_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_a_3149_ = lean_ctor_get(v___x_3139_, 0);
v_a_3150_ = lean_ctor_get(v___x_3139_, 1);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3139_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_inc(v_a_3149_);
lean_dec(v___x_3139_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3149_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1___boxed(lean_object* v_x_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintroError__1(v_x_3158_, v_a_3159_, v_a_3160_);
lean_dec_ref(v_a_3159_);
return v_res_3161_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__2));
v___x_3170_ = l_String_toRawSubstring_x27(v___x_3169_);
return v___x_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(lean_object* v_x_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v___x_3178_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__0));
v___x_3179_ = ((lean_object*)(l_Lean_Parser_Tactic_mintro___closed__1));
lean_inc(v_x_3175_);
v___x_3180_ = l_Lean_Syntax_isOfKind(v_x_3175_, v___x_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
lean_dec(v_x_3175_);
v___x_3181_ = lean_box(1);
v___x_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3181_);
lean_ctor_set(v___x_3182_, 1, v_a_3177_);
return v___x_3182_;
}
else
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3183_ = lean_unsigned_to_nat(0u);
v___x_3184_ = lean_unsigned_to_nat(1u);
v___x_3185_ = l_Lean_Syntax_getArg(v_x_3175_, v___x_3184_);
lean_dec(v_x_3175_);
v___x_3186_ = lean_unsigned_to_nat(2u);
v___x_3187_ = l_Lean_Syntax_getNumArgs(v___x_3185_);
v___x_3188_ = lean_nat_dec_le(v___x_3186_, v___x_3187_);
if (v___x_3188_ == 0)
{
uint8_t v___x_3189_; 
lean_dec(v___x_3187_);
lean_inc(v___x_3185_);
v___x_3189_ = l_Lean_Syntax_matchesNull(v___x_3185_, v___x_3184_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec(v___x_3185_);
v___x_3190_ = lean_box(1);
v___x_3191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v_a_3177_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v___x_3192_ = l_Lean_Syntax_getArg(v___x_3185_, v___x_3183_);
lean_dec(v___x_3185_);
v___x_3193_ = ((lean_object*)(l_Lean_Parser_Tactic_mintroPat___00__closed__1));
lean_inc(v___x_3192_);
v___x_3194_ = l_Lean_Syntax_isOfKind(v___x_3192_, v___x_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec(v___x_3192_);
v___x_3195_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3177_);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = l_Lean_Syntax_getArg(v___x_3192_, v___x_3183_);
lean_dec(v___x_3192_);
v___x_3197_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPat___00__closed__1));
lean_inc(v___x_3196_);
v___x_3198_ = l_Lean_Syntax_isOfKind(v___x_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v_quotContext_3199_; lean_object* v_currMacroScope_3200_; lean_object* v_ref_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v_quotContext_3199_ = lean_ctor_get(v_a_3176_, 1);
v_currMacroScope_3200_ = lean_ctor_get(v_a_3176_, 2);
v_ref_3201_ = lean_ctor_get(v_a_3176_, 5);
v___x_3202_ = l_Lean_SourceInfo_fromRef(v_ref_3201_, v___x_3198_);
v___x_3203_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3204_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3202_, 12);
v___x_3205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3202_);
lean_ctor_set(v___x_3205_, 1, v___x_3178_);
v___x_3206_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3207_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3208_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3200_);
lean_inc(v_quotContext_3199_);
v___x_3209_ = l_Lean_addMacroScope(v_quotContext_3199_, v___x_3208_, v_currMacroScope_3200_);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3202_);
lean_ctor_set(v___x_3211_, 1, v___x_3207_);
lean_ctor_set(v___x_3211_, 2, v___x_3209_);
lean_ctor_set(v___x_3211_, 3, v___x_3210_);
lean_inc_ref(v___x_3211_);
v___x_3212_ = l_Lean_Syntax_node1(v___x_3202_, v___x_3206_, v___x_3211_);
v___x_3213_ = l_Lean_Syntax_node1(v___x_3202_, v___x_3197_, v___x_3212_);
v___x_3214_ = l_Lean_Syntax_node1(v___x_3202_, v___x_3193_, v___x_3213_);
v___x_3215_ = l_Lean_Syntax_node1(v___x_3202_, v___x_3204_, v___x_3214_);
v___x_3216_ = l_Lean_Syntax_node2(v___x_3202_, v___x_3179_, v___x_3205_, v___x_3215_);
v___x_3217_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3202_);
lean_ctor_set(v___x_3218_, 1, v___x_3217_);
v___x_3219_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3220_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3202_);
lean_ctor_set(v___x_3221_, 1, v___x_3219_);
v___x_3222_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3223_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3202_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = l_Lean_Syntax_node4(v___x_3202_, v___x_3220_, v___x_3221_, v___x_3211_, v___x_3223_, v___x_3196_);
v___x_3225_ = l_Lean_Syntax_node3(v___x_3202_, v___x_3204_, v___x_3216_, v___x_3218_, v___x_3224_);
v___x_3226_ = l_Lean_Syntax_node1(v___x_3202_, v___x_3203_, v___x_3225_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v_a_3177_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3228_ = l_Lean_Syntax_getArg(v___x_3196_, v___x_3183_);
v___x_3229_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__3));
v___x_3230_ = l_Lean_Syntax_isOfKind(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v_quotContext_3231_; lean_object* v_currMacroScope_3232_; lean_object* v_ref_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_quotContext_3231_ = lean_ctor_get(v_a_3176_, 1);
v_currMacroScope_3232_ = lean_ctor_get(v_a_3176_, 2);
v_ref_3233_ = lean_ctor_get(v_a_3176_, 5);
v___x_3234_ = l_Lean_SourceInfo_fromRef(v_ref_3233_, v___x_3230_);
v___x_3235_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
v___x_3236_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
lean_inc_n(v___x_3234_, 12);
v___x_3237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3234_);
lean_ctor_set(v___x_3237_, 1, v___x_3178_);
v___x_3238_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__3);
v___x_3239_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__4));
lean_inc(v_currMacroScope_3232_);
lean_inc(v_quotContext_3231_);
v___x_3240_ = l_Lean_addMacroScope(v_quotContext_3231_, v___x_3239_, v_currMacroScope_3232_);
v___x_3241_ = lean_box(0);
v___x_3242_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3234_);
lean_ctor_set(v___x_3242_, 1, v___x_3238_);
lean_ctor_set(v___x_3242_, 2, v___x_3240_);
lean_ctor_set(v___x_3242_, 3, v___x_3241_);
lean_inc_ref(v___x_3242_);
v___x_3243_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3229_, v___x_3242_);
v___x_3244_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3197_, v___x_3243_);
v___x_3245_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3193_, v___x_3244_);
v___x_3246_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3236_, v___x_3245_);
v___x_3247_ = l_Lean_Syntax_node2(v___x_3234_, v___x_3179_, v___x_3237_, v___x_3246_);
v___x_3248_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3234_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__0));
v___x_3251_ = ((lean_object*)(l_Lean_Parser_Tactic_mcases___closed__1));
v___x_3252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3234_);
lean_ctor_set(v___x_3252_, 1, v___x_3250_);
v___x_3253_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__6));
v___x_3254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3234_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_Lean_Syntax_node4(v___x_3234_, v___x_3251_, v___x_3252_, v___x_3242_, v___x_3254_, v___x_3196_);
v___x_3256_ = l_Lean_Syntax_node3(v___x_3234_, v___x_3236_, v___x_3247_, v___x_3249_, v___x_3255_);
v___x_3257_ = l_Lean_Syntax_node1(v___x_3234_, v___x_3235_, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
lean_ctor_set(v___x_3258_, 1, v_a_3177_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; 
lean_dec(v___x_3196_);
v___x_3259_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3177_);
return v___x_3259_;
}
}
}
}
}
else
{
lean_object* v_ref_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v_pats_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v_ref_3260_ = lean_ctor_get(v_a_3176_, 5);
v___x_3261_ = l_Lean_Syntax_getArg(v___x_3185_, v___x_3183_);
v___x_3262_ = l_Lean_Syntax_getArg(v___x_3185_, v___x_3184_);
v___x_3263_ = l_Lean_Syntax_getArgs(v___x_3185_);
lean_dec(v___x_3185_);
v___x_3264_ = l_Array_extract___redArg(v___x_3263_, v___x_3186_, v___x_3187_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3266_ = lean_box(2);
v___x_3267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___x_3265_);
lean_ctor_set(v___x_3267_, 2, v___x_3264_);
v_pats_3268_ = l_Lean_Syntax_getArgs(v___x_3267_);
lean_dec_ref_known(v___x_3267_, 3);
v___x_3269_ = 0;
v___x_3270_ = l_Lean_SourceInfo_fromRef(v_ref_3260_, v___x_3269_);
v___x_3271_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3270_, 7);
v___x_3272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3178_);
v___x_3273_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3265_, v___x_3261_);
lean_inc_ref(v___x_3272_);
v___x_3274_ = l_Lean_Syntax_node2(v___x_3270_, v___x_3179_, v___x_3272_, v___x_3273_);
v___x_3275_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3270_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Array_mkArray1___redArg(v___x_3262_);
v___x_3278_ = l_Array_append___redArg(v___x_3277_, v_pats_3268_);
lean_dec_ref(v_pats_3268_);
v___x_3279_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3270_);
lean_ctor_set(v___x_3279_, 1, v___x_3265_);
lean_ctor_set(v___x_3279_, 2, v___x_3278_);
v___x_3280_ = l_Lean_Syntax_node2(v___x_3270_, v___x_3179_, v___x_3272_, v___x_3279_);
v___x_3281_ = l_Lean_Syntax_node3(v___x_3270_, v___x_3265_, v___x_3274_, v___x_3276_, v___x_3280_);
v___x_3282_ = l_Lean_Syntax_node1(v___x_3270_, v___x_3271_, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_a_3177_);
return v___x_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___boxed(lean_object* v_x_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1(v_x_3284_, v_a_3285_, v_a_3286_);
lean_dec_ref(v_a_3285_);
return v_res_3287_;
}
}
static lean_object* _init_l_Lean_Parser_Category_mrevertPat(void){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_box(0);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(lean_object* v_x_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevertError___closed__1));
v___x_3393_ = l_Lean_Syntax_isOfKind(v_x_3389_, v___x_3392_);
if (v___x_3393_ == 0)
{
lean_object* v___x_3394_; lean_object* v___x_3395_; 
v___x_3394_ = lean_box(1);
v___x_3395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v_a_3391_);
return v___x_3395_;
}
else
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___closed__0));
v___x_3397_ = l_Lean_Macro_throwError___redArg(v___x_3396_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_a_3399_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3397_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3398_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v_a_3407_ = lean_ctor_get(v___x_3397_, 0);
v_a_3408_ = lean_ctor_get(v___x_3397_, 1);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3397_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_inc(v_a_3407_);
lean_dec(v___x_3397_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3407_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1___boxed(lean_object* v_x_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevertError__1(v_x_3416_, v_a_3417_, v_a_3418_);
lean_dec_ref(v_a_3417_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(lean_object* v_x_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
v___x_3423_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__0));
v___x_3424_ = ((lean_object*)(l_Lean_Parser_Tactic_mrevert___closed__1));
lean_inc(v_x_3420_);
v___x_3425_ = l_Lean_Syntax_isOfKind(v_x_3420_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_dec(v_x_3420_);
v___x_3426_ = lean_box(1);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3426_);
lean_ctor_set(v___x_3427_, 1, v_a_3422_);
return v___x_3427_;
}
else
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; uint8_t v___x_3432_; 
v___x_3428_ = lean_unsigned_to_nat(1u);
v___x_3429_ = l_Lean_Syntax_getArg(v_x_3420_, v___x_3428_);
lean_dec(v_x_3420_);
v___x_3430_ = lean_unsigned_to_nat(2u);
v___x_3431_ = l_Lean_Syntax_getNumArgs(v___x_3429_);
v___x_3432_ = lean_nat_dec_le(v___x_3430_, v___x_3431_);
if (v___x_3432_ == 0)
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v___x_3431_);
lean_dec(v___x_3429_);
v___x_3433_ = lean_box(1);
v___x_3434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v_a_3422_);
return v___x_3434_;
}
else
{
lean_object* v_ref_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_pats_3444_; uint8_t v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_ref_3435_ = lean_ctor_get(v_a_3421_, 5);
v___x_3436_ = lean_unsigned_to_nat(0u);
v___x_3437_ = l_Lean_Syntax_getArg(v___x_3429_, v___x_3436_);
v___x_3438_ = l_Lean_Syntax_getArg(v___x_3429_, v___x_3428_);
v___x_3439_ = l_Lean_Syntax_getArgs(v___x_3429_);
lean_dec(v___x_3429_);
v___x_3440_ = l_Array_extract___redArg(v___x_3439_, v___x_3430_, v___x_3431_);
lean_dec_ref(v___x_3439_);
v___x_3441_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3442_ = lean_box(2);
v___x_3443_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v___x_3441_);
lean_ctor_set(v___x_3443_, 2, v___x_3440_);
v_pats_3444_ = l_Lean_Syntax_getArgs(v___x_3443_);
lean_dec_ref_known(v___x_3443_, 3);
v___x_3445_ = 0;
v___x_3446_ = l_Lean_SourceInfo_fromRef(v_ref_3435_, v___x_3445_);
v___x_3447_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__1));
lean_inc_n(v___x_3446_, 7);
v___x_3448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3446_);
lean_ctor_set(v___x_3448_, 1, v___x_3423_);
v___x_3449_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3441_, v___x_3437_);
lean_inc_ref(v___x_3448_);
v___x_3450_ = l_Lean_Syntax_node2(v___x_3446_, v___x_3424_, v___x_3448_, v___x_3449_);
v___x_3451_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3446_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l_Array_mkArray1___redArg(v___x_3438_);
v___x_3454_ = l_Array_append___redArg(v___x_3453_, v_pats_3444_);
lean_dec_ref(v_pats_3444_);
v___x_3455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3446_);
lean_ctor_set(v___x_3455_, 1, v___x_3441_);
lean_ctor_set(v___x_3455_, 2, v___x_3454_);
v___x_3456_ = l_Lean_Syntax_node2(v___x_3446_, v___x_3424_, v___x_3448_, v___x_3455_);
v___x_3457_ = l_Lean_Syntax_node3(v___x_3446_, v___x_3441_, v___x_3450_, v___x_3452_, v___x_3456_);
v___x_3458_ = l_Lean_Syntax_node1(v___x_3446_, v___x_3447_, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_a_3422_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1___boxed(lean_object* v_x_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mrevert__1(v_x_3460_, v_a_3461_, v_a_3462_);
lean_dec_ref(v_a_3461_);
return v_res_3463_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__7));
v___x_3530_ = l_Lean_mkIdent(v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(lean_object* v_x_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3560_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3603_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
lean_inc(v_x_3532_);
v___x_3604_ = l_Lean_Syntax_isOfKind(v_x_3532_, v___x_3603_);
if (v___x_3604_ == 0)
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_dec(v_x_3532_);
v___x_3605_ = lean_box(1);
v___x_3606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v_a_3534_);
return v___x_3606_;
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3607_ = lean_unsigned_to_nat(1u);
v___x_3608_ = l_Lean_Syntax_getArg(v_x_3532_, v___x_3607_);
lean_dec(v_x_3532_);
v___x_3609_ = l_Lean_Syntax_getOptional_x3f(v___x_3608_);
lean_dec(v___x_3608_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_box(0);
v___y_3560_ = v___x_3610_;
goto v___jp_3559_;
}
else
{
lean_object* v_val_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v_val_3611_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3609_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_val_3611_);
lean_dec(v___x_3609_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_val_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
v___y_3560_ = v___x_3616_;
goto v___jp_3559_;
}
}
}
}
v___jp_3535_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_inc_ref(v___y_3539_);
v___x_3550_ = l_Array_append___redArg(v___y_3539_, v___y_3549_);
lean_dec_ref(v___y_3549_);
lean_inc(v___y_3542_);
lean_inc_n(v___y_3544_, 6);
v___x_3551_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3551_, 0, v___y_3544_);
lean_ctor_set(v___x_3551_, 1, v___y_3542_);
lean_ctor_set(v___x_3551_, 2, v___x_3550_);
v___x_3552_ = l_Lean_Syntax_node2(v___y_3544_, v___y_3537_, v___y_3543_, v___x_3551_);
lean_inc(v___y_3536_);
v___x_3553_ = l_Lean_Syntax_node3(v___y_3544_, v___y_3536_, v___y_3547_, v___y_3540_, v___x_3552_);
v___x_3554_ = l_Lean_Syntax_node1(v___y_3544_, v___y_3542_, v___x_3553_);
v___x_3555_ = l_Lean_Syntax_node1(v___y_3544_, v___y_3538_, v___x_3554_);
v___x_3556_ = l_Lean_Syntax_node1(v___y_3544_, v___y_3545_, v___x_3555_);
v___x_3557_ = l_Lean_Syntax_node3(v___y_3544_, v___y_3546_, v___y_3548_, v___x_3556_, v___y_3541_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
lean_ctor_set(v___x_3558_, 1, v_a_3534_);
return v___x_3558_;
}
v___jp_3559_:
{
lean_object* v_ref_3561_; uint8_t v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_ref_3561_ = lean_ctor_get(v_a_3533_, 5);
v___x_3562_ = 0;
v___x_3563_ = l_Lean_SourceInfo_fromRef(v_ref_3561_, v___x_3562_);
v___x_3564_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3565_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3563_, 20);
v___x_3566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3563_);
lean_ctor_set(v___x_3566_, 1, v___x_3565_);
v___x_3567_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3568_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3569_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3570_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__1));
v___x_3571_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3572_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3563_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__3));
v___x_3575_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__4));
v___x_3576_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3563_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__1));
v___x_3578_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoBind___closed__2));
v___x_3579_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3563_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__8);
v___x_3581_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3569_, v___x_3580_);
lean_inc_ref(v___x_3579_);
v___x_3582_ = l_Lean_Syntax_node2(v___x_3563_, v___x_3577_, v___x_3579_, v___x_3581_);
v___x_3583_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3569_, v___x_3582_);
v___x_3584_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3568_, v___x_3583_);
v___x_3585_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3567_, v___x_3584_);
v___x_3586_ = l_Lean_Syntax_node2(v___x_3563_, v___x_3574_, v___x_3576_, v___x_3585_);
v___x_3587_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3569_, v___x_3586_);
v___x_3588_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3568_, v___x_3587_);
v___x_3589_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3567_, v___x_3588_);
v___x_3590_ = l_Lean_Syntax_node2(v___x_3563_, v___x_3571_, v___x_3573_, v___x_3589_);
v___x_3591_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3569_, v___x_3590_);
v___x_3592_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3568_, v___x_3591_);
v___x_3593_ = l_Lean_Syntax_node1(v___x_3563_, v___x_3567_, v___x_3592_);
v___x_3594_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3563_);
lean_ctor_set(v___x_3595_, 1, v___x_3594_);
lean_inc_ref(v___x_3595_);
lean_inc_ref(v___x_3566_);
v___x_3596_ = l_Lean_Syntax_node3(v___x_3563_, v___x_3564_, v___x_3566_, v___x_3593_, v___x_3595_);
v___x_3597_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___closed__9));
v___x_3598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3563_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3560_) == 1)
{
lean_object* v_val_3600_; lean_object* v___x_3601_; 
v_val_3600_ = lean_ctor_get(v___y_3560_, 0);
lean_inc(v_val_3600_);
lean_dec_ref_known(v___y_3560_, 1);
v___x_3601_ = l_Array_mkArray1___redArg(v_val_3600_);
v___y_3536_ = v___x_3570_;
v___y_3537_ = v___x_3577_;
v___y_3538_ = v___x_3568_;
v___y_3539_ = v___x_3599_;
v___y_3540_ = v___x_3598_;
v___y_3541_ = v___x_3595_;
v___y_3542_ = v___x_3569_;
v___y_3543_ = v___x_3579_;
v___y_3544_ = v___x_3563_;
v___y_3545_ = v___x_3567_;
v___y_3546_ = v___x_3564_;
v___y_3547_ = v___x_3596_;
v___y_3548_ = v___x_3566_;
v___y_3549_ = v___x_3601_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3602_; 
lean_dec(v___y_3560_);
v___x_3602_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3536_ = v___x_3570_;
v___y_3537_ = v___x_3577_;
v___y_3538_ = v___x_3568_;
v___y_3539_ = v___x_3599_;
v___y_3540_ = v___x_3598_;
v___y_3541_ = v___x_3595_;
v___y_3542_ = v___x_3569_;
v___y_3543_ = v___x_3579_;
v___y_3544_ = v___x_3563_;
v___y_3545_ = v___x_3567_;
v___y_3546_ = v___x_3564_;
v___y_3547_ = v___x_3596_;
v___y_3548_ = v___x_3566_;
v___y_3549_ = v___x_3602_;
goto v___jp_3535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1___boxed(lean_object* v_x_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspecNoSimp__1(v_x_3619_, v_a_3620_, v_a_3621_);
lean_dec_ref(v_a_3620_);
return v_res_3622_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__4));
v___x_3655_ = l_Lean_mkIdent(v___x_3654_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(lean_object* v_x_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3751_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3768_ = ((lean_object*)(l_Lean_Parser_Tactic_mspec___closed__1));
lean_inc(v_x_3663_);
v___x_3769_ = l_Lean_Syntax_isOfKind(v_x_3663_, v___x_3768_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_dec(v_x_3663_);
v___x_3770_ = lean_box(1);
v___x_3771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3770_);
lean_ctor_set(v___x_3771_, 1, v_a_3665_);
return v___x_3771_;
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_unsigned_to_nat(1u);
v___x_3773_ = l_Lean_Syntax_getArg(v_x_3663_, v___x_3772_);
lean_dec(v_x_3663_);
v___x_3774_ = l_Lean_Syntax_getOptional_x3f(v___x_3773_);
lean_dec(v___x_3773_);
if (lean_obj_tag(v___x_3774_) == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = lean_box(0);
v___y_3751_ = v___x_3775_;
goto v___jp_3750_;
}
else
{
lean_object* v_val_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_val_3776_ = lean_ctor_get(v___x_3774_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3774_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3774_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_val_3776_);
lean_dec(v___x_3774_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_val_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
v___y_3751_ = v___x_3781_;
goto v___jp_3750_;
}
}
}
}
v___jp_3666_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_inc_ref_n(v___y_3671_, 2);
v___x_3677_ = l_Array_append___redArg(v___y_3671_, v___y_3676_);
lean_dec_ref(v___y_3676_);
lean_inc_n(v___y_3675_, 12);
lean_inc_n(v___y_3670_, 50);
v___x_3678_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3678_, 0, v___y_3670_);
lean_ctor_set(v___x_3678_, 1, v___y_3675_);
lean_ctor_set(v___x_3678_, 2, v___x_3677_);
lean_inc(v___y_3668_);
v___x_3679_ = l_Lean_Syntax_node2(v___y_3670_, v___y_3668_, v___y_3673_, v___x_3678_);
v___x_3680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3680_, 0, v___y_3670_);
lean_ctor_set(v___x_3680_, 1, v___y_3675_);
lean_ctor_set(v___x_3680_, 2, v___y_3671_);
v___x_3681_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__1));
v___x_3682_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__2));
v___x_3683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___y_3670_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3685_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___y_3670_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__12));
v___x_3688_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__13));
v___x_3689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3689_, 0, v___y_3670_);
lean_ctor_set(v___x_3689_, 1, v___x_3687_);
v___x_3690_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__15));
lean_inc_ref_n(v___x_3680_, 8);
v___x_3691_ = l_Lean_Syntax_node1(v___y_3670_, v___x_3690_, v___x_3680_);
v___x_3692_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__17));
v___x_3693_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___y_3670_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3675_, v___x_3693_);
v___x_3695_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__18));
v___x_3696_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___y_3670_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__20));
v___x_3698_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__5);
v___x_3699_ = l_Lean_Syntax_node3(v___y_3670_, v___x_3697_, v___x_3680_, v___x_3680_, v___x_3698_);
v___x_3700_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_3701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___y_3670_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__29);
v___x_3703_ = l_Lean_Syntax_node3(v___y_3670_, v___x_3697_, v___x_3680_, v___x_3680_, v___x_3702_);
v___x_3704_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3675_, v___x_3699_, v___x_3701_, v___x_3703_);
v___x_3705_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__156));
v___x_3706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___y_3670_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3675_, v___x_3696_, v___x_3704_, v___x_3706_);
v___x_3708_ = l_Lean_Syntax_node6(v___y_3670_, v___x_3688_, v___x_3689_, v___x_3691_, v___x_3680_, v___x_3694_, v___x_3707_, v___x_3680_);
v___x_3709_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3675_, v___x_3708_);
lean_inc_n(v___y_3667_, 7);
v___x_3710_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3709_);
lean_inc_n(v___y_3674_, 7);
v___x_3711_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3710_);
lean_inc_ref(v___x_3686_);
v___x_3712_ = l_Lean_Syntax_node2(v___y_3670_, v___x_3684_, v___x_3686_, v___x_3711_);
v___x_3713_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3675_, v___x_3712_);
v___x_3714_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3713_);
v___x_3715_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3714_);
v___x_3716_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3717_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___y_3670_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
lean_inc_ref_n(v___x_3717_, 3);
lean_inc_n(v___y_3669_, 3);
lean_inc_n(v___y_3672_, 4);
v___x_3718_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3672_, v___y_3669_, v___x_3715_, v___x_3717_);
v___x_3719_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3720_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___y_3670_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = l_Lean_Syntax_node1(v___y_3670_, v___x_3719_, v___x_3721_);
v___x_3723_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___y_3670_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3726_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3727_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___y_3670_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = l_Lean_Syntax_node1(v___y_3670_, v___x_3725_, v___x_3727_);
v___x_3729_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3675_, v___x_3722_, v___x_3724_, v___x_3728_);
v___x_3730_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3729_);
v___x_3731_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3730_);
v___x_3732_ = l_Lean_Syntax_node2(v___y_3670_, v___x_3684_, v___x_3686_, v___x_3731_);
v___x_3733_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3675_, v___x_3732_);
v___x_3734_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3733_);
v___x_3735_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3734_);
v___x_3736_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3672_, v___y_3669_, v___x_3735_, v___x_3717_);
v___x_3737_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3675_, v___x_3718_, v___x_3680_, v___x_3736_);
v___x_3738_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3737_);
v___x_3739_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3738_);
v___x_3740_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3672_, v___y_3669_, v___x_3739_, v___x_3717_);
v___x_3741_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3675_, v___x_3740_);
v___x_3742_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3741_);
v___x_3743_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3742_);
v___x_3744_ = l_Lean_Syntax_node2(v___y_3670_, v___x_3681_, v___x_3683_, v___x_3743_);
v___x_3745_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3675_, v___x_3679_, v___x_3680_, v___x_3744_);
v___x_3746_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3667_, v___x_3745_);
v___x_3747_ = l_Lean_Syntax_node1(v___y_3670_, v___y_3674_, v___x_3746_);
v___x_3748_ = l_Lean_Syntax_node3(v___y_3670_, v___y_3672_, v___y_3669_, v___x_3747_, v___x_3717_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v_a_3665_);
return v___x_3749_;
}
v___jp_3750_:
{
lean_object* v_ref_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_ref_3752_ = lean_ctor_get(v_a_3664_, 5);
v___x_3753_ = 0;
v___x_3754_ = l_Lean_SourceInfo_fromRef(v_ref_3752_, v___x_3753_);
v___x_3755_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3756_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
lean_inc_n(v___x_3754_, 2);
v___x_3757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3754_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3759_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3760_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3761_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__1));
v___x_3762_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecNoSimp___closed__2));
v___x_3763_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3754_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = lean_obj_once(&l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16, &l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16_once, _init_l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__16);
if (lean_obj_tag(v___y_3751_) == 1)
{
lean_object* v_val_3765_; lean_object* v___x_3766_; 
v_val_3765_ = lean_ctor_get(v___y_3751_, 0);
lean_inc(v_val_3765_);
lean_dec_ref_known(v___y_3751_, 1);
v___x_3766_ = l_Array_mkArray1___redArg(v_val_3765_);
v___y_3667_ = v___x_3759_;
v___y_3668_ = v___x_3761_;
v___y_3669_ = v___x_3757_;
v___y_3670_ = v___x_3754_;
v___y_3671_ = v___x_3764_;
v___y_3672_ = v___x_3755_;
v___y_3673_ = v___x_3763_;
v___y_3674_ = v___x_3758_;
v___y_3675_ = v___x_3760_;
v___y_3676_ = v___x_3766_;
goto v___jp_3666_;
}
else
{
lean_object* v___x_3767_; 
lean_dec(v___y_3751_);
v___x_3767_ = ((lean_object*)(l_Lean_Parser_Tactic_MCasesPat_parse_go___closed__0));
v___y_3667_ = v___x_3759_;
v___y_3668_ = v___x_3761_;
v___y_3669_ = v___x_3757_;
v___y_3670_ = v___x_3754_;
v___y_3671_ = v___x_3764_;
v___y_3672_ = v___x_3755_;
v___y_3673_ = v___x_3763_;
v___y_3674_ = v___x_3758_;
v___y_3675_ = v___x_3760_;
v___y_3676_ = v___x_3767_;
goto v___jp_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___boxed(lean_object* v_x_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1(v_x_3784_, v_a_3785_, v_a_3786_);
lean_dec_ref(v_a_3785_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(lean_object* v_x_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_){
_start:
{
lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3831_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial___closed__1));
v___x_3832_ = l_Lean_Syntax_isOfKind(v_x_3828_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3833_ = lean_box(1);
v___x_3834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
lean_ctor_set(v___x_3834_, 1, v_a_3830_);
return v___x_3834_;
}
else
{
lean_object* v_ref_3835_; uint8_t v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_ref_3835_ = lean_ctor_get(v_a_3829_, 5);
v___x_3836_ = 0;
v___x_3837_ = l_Lean_SourceInfo_fromRef(v_ref_3835_, v___x_3836_);
v___x_3838_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__0));
v___x_3839_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__1));
lean_inc_n(v___x_3837_, 33);
v___x_3840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3837_);
lean_ctor_set(v___x_3840_, 1, v___x_3838_);
v___x_3841_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__8));
v___x_3842_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__3));
v___x_3843_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___closed__4));
v___x_3844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3837_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
v___x_3845_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__4));
v___x_3846_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__6));
v___x_3847_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__1));
v___x_3848_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__2));
v___x_3849_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3837_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__10));
v___x_3851_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__11));
v___x_3852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3837_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__1));
v___x_3854_ = ((lean_object*)(l_Lean_Parser_Tactic_mpureIntro___closed__2));
v___x_3855_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3837_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3853_, v___x_3855_);
v___x_3857_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3841_, v___x_3856_);
v___x_3858_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3846_, v___x_3857_);
v___x_3859_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3845_, v___x_3858_);
lean_inc_ref(v___x_3852_);
v___x_3860_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3850_, v___x_3852_, v___x_3859_);
v___x_3861_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3841_, v___x_3860_);
v___x_3862_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3846_, v___x_3861_);
v___x_3863_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3845_, v___x_3862_);
v___x_3864_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mleave__1___closed__163));
v___x_3865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3837_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l_Lean_Syntax_node3(v___x_3837_, v___x_3847_, v___x_3849_, v___x_3863_, v___x_3865_);
v___x_3867_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mintro__1___closed__5));
v___x_3868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3837_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__7));
v___x_3870_ = ((lean_object*)(l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__mspec__1___closed__8));
v___x_3871_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3837_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3869_, v___x_3871_);
v___x_3873_ = l_Lean_Syntax_node3(v___x_3837_, v___x_3841_, v___x_3866_, v___x_3868_, v___x_3872_);
v___x_3874_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3846_, v___x_3873_);
v___x_3875_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3845_, v___x_3874_);
lean_inc_ref(v___x_3844_);
v___x_3876_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3842_, v___x_3844_, v___x_3875_);
v___x_3877_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__1));
v___x_3878_ = ((lean_object*)(l_Lean_Parser_Tactic_tacticMvcgen__trivial__extensible___closed__2));
v___x_3879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3837_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
v___x_3880_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3877_, v___x_3879_);
v___x_3881_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3841_, v___x_3880_);
v___x_3882_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3846_, v___x_3881_);
v___x_3883_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3845_, v___x_3882_);
v___x_3884_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3850_, v___x_3852_, v___x_3883_);
v___x_3885_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3841_, v___x_3884_);
v___x_3886_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3846_, v___x_3885_);
v___x_3887_ = l_Lean_Syntax_node1(v___x_3837_, v___x_3845_, v___x_3886_);
v___x_3888_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3842_, v___x_3844_, v___x_3887_);
v___x_3889_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3841_, v___x_3876_, v___x_3888_);
v___x_3890_ = l_Lean_Syntax_node2(v___x_3837_, v___x_3839_, v___x_3840_, v___x_3889_);
v___x_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
lean_ctor_set(v___x_3891_, 1, v_a_3830_);
return v___x_3891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1___boxed(lean_object* v_x_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_Parser_Tactic___aux__Std__Tactic__Do__Syntax______macroRules__Lean__Parser__Tactic__tacticMvcgen__trivial__1(v_x_3892_, v_a_3893_, v_a_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3895_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__8(void){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3913_ = l_Lean_cdotTk;
v___x_3914_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__7));
v___x_3915_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3916_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3914_);
lean_ctor_set(v___x_3916_, 2, v___x_3913_);
return v___x_3916_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__13(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3926_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_3927_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__8, &l_Lean_Parser_Tactic_invariantDotAlt___closed__8_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__8);
v___x_3928_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3929_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
lean_ctor_set(v___x_3929_, 1, v___x_3927_);
lean_ctor_set(v___x_3929_, 2, v___x_3926_);
return v___x_3929_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__14(void){
_start:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3930_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__13, &l_Lean_Parser_Tactic_invariantDotAlt___closed__13_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__13);
v___x_3931_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__1));
v___x_3932_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__0));
v___x_3933_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
lean_ctor_set(v___x_3933_, 1, v___x_3931_);
lean_ctor_set(v___x_3933_, 2, v___x_3930_);
return v___x_3933_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantDotAlt(void){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantDotAlt___closed__14, &l_Lean_Parser_Tactic_invariantDotAlt___closed__14_once, _init_l_Lean_Parser_Tactic_invariantDotAlt___closed__14);
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3948_ = l_Lean_Parser_Tactic_caseArg;
v___x_3949_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__4));
v___x_3950_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3951_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v___x_3949_);
lean_ctor_set(v___x_3951_, 2, v___x_3948_);
return v___x_3951_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__6(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3952_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_3953_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__5, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__5_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__5);
v___x_3954_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3955_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
lean_ctor_set(v___x_3955_, 1, v___x_3953_);
lean_ctor_set(v___x_3955_, 2, v___x_3952_);
return v___x_3955_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__7(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3956_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_3957_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__6, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__6_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__6);
v___x_3958_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_3959_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v___x_3957_);
lean_ctor_set(v___x_3959_, 2, v___x_3956_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3960_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__7, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__7_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__7);
v___x_3961_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__1));
v___x_3962_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__0));
v___x_3963_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v___x_3961_);
lean_ctor_set(v___x_3963_, 2, v___x_3960_);
return v___x_3963_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantCaseAlt(void){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantCaseAlt___closed__8, &l_Lean_Parser_Tactic_invariantCaseAlt___closed__8_once, _init_l_Lean_Parser_Tactic_invariantCaseAlt___closed__8);
return v___x_3964_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__4(void){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4015_ = l_Lean_Parser_Tactic_invariantCaseAlt;
v___x_4016_ = l_Lean_Parser_Tactic_invariantDotAlt;
v___x_4017_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4018_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
lean_ctor_set(v___x_4018_, 1, v___x_4016_);
lean_ctor_set(v___x_4018_, 2, v___x_4015_);
return v___x_4018_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__5(void){
_start:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__4, &l_Lean_Parser_Tactic_invariantAlts___closed__4_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__4);
v___x_4020_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__11));
v___x_4021_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4022_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
lean_ctor_set(v___x_4022_, 1, v___x_4020_);
lean_ctor_set(v___x_4022_, 2, v___x_4019_);
return v___x_4022_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__6(void){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4023_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__5, &l_Lean_Parser_Tactic_invariantAlts___closed__5_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__5);
v___x_4024_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_4025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
lean_ctor_set(v___x_4025_, 1, v___x_4023_);
return v___x_4025_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__7(void){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__6, &l_Lean_Parser_Tactic_invariantAlts___closed__6_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__6);
v___x_4027_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_4028_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v___x_4026_);
return v___x_4028_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__8(void){
_start:
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4029_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__7, &l_Lean_Parser_Tactic_invariantAlts___closed__7_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__7);
v___x_4030_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW));
v___x_4031_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4032_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
lean_ctor_set(v___x_4032_, 1, v___x_4030_);
lean_ctor_set(v___x_4032_, 2, v___x_4029_);
return v___x_4032_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts___closed__9(void){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4033_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__8, &l_Lean_Parser_Tactic_invariantAlts___closed__8_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__8);
v___x_4034_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__1));
v___x_4035_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__0));
v___x_4036_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
lean_ctor_set(v___x_4036_, 1, v___x_4034_);
lean_ctor_set(v___x_4036_, 2, v___x_4033_);
return v___x_4036_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_invariantAlts(void){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_obj_once(&l_Lean_Parser_Tactic_invariantAlts___closed__9, &l_Lean_Parser_Tactic_invariantAlts___closed__9_once, _init_l_Lean_Parser_Tactic_invariantAlts___closed__9);
return v___x_4037_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__3(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = lean_obj_once(&l_Lean_Parser_Tactic_mrenameI___closed__7, &l_Lean_Parser_Tactic_mrenameI___closed__7_once, _init_l_Lean_Parser_Tactic_mrenameI___closed__7);
v___x_4049_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_4050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___x_4048_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__4(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4051_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__3, &l_Lean_Parser_Tactic_frameAlt___closed__3_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__3);
v___x_4052_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__2));
v___x_4053_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4054_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
lean_ctor_set(v___x_4054_, 1, v___x_4052_);
lean_ctor_set(v___x_4054_, 2, v___x_4051_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__5(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4055_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_4056_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__4, &l_Lean_Parser_Tactic_frameAlt___closed__4_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__4);
v___x_4057_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4058_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v___x_4056_);
lean_ctor_set(v___x_4058_, 2, v___x_4055_);
return v___x_4058_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__6(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4059_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__12));
v___x_4060_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__5, &l_Lean_Parser_Tactic_frameAlt___closed__5_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__5);
v___x_4061_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4062_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___x_4060_);
lean_ctor_set(v___x_4062_, 2, v___x_4059_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt___closed__7(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__6, &l_Lean_Parser_Tactic_frameAlt___closed__6_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__6);
v___x_4064_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__1));
v___x_4065_ = ((lean_object*)(l_Lean_Parser_Tactic_frameAlt___closed__0));
v___x_4066_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
lean_ctor_set(v___x_4066_, 1, v___x_4064_);
lean_ctor_set(v___x_4066_, 2, v___x_4063_);
return v___x_4066_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_frameAlt(void){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = lean_obj_once(&l_Lean_Parser_Tactic_frameAlt___closed__7, &l_Lean_Parser_Tactic_frameAlt___closed__7_once, _init_l_Lean_Parser_Tactic_frameAlt___closed__7);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__2(void){
_start:
{
uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4074_ = 0;
v___x_4075_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__3));
v___x_4076_ = ((lean_object*)(l_Lean_Parser_Tactic_mcasesPatAlts___closed__2));
v___x_4077_ = l_Lean_Parser_Tactic_caseArg;
v___x_4078_ = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
lean_ctor_set(v___x_4078_, 1, v___x_4076_);
lean_ctor_set(v___x_4078_, 2, v___x_4075_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*3, v___x_4074_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__3(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4079_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__2, &l_Lean_Parser_Tactic_vcAlt___closed__2_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__2);
v___x_4080_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantCaseAlt___closed__3));
v___x_4081_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4082_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v___x_4080_);
lean_ctor_set(v___x_4082_, 2, v___x_4079_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__4(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4083_ = ((lean_object*)(l_Lean_Parser_Tactic_mdup___closed__5));
v___x_4084_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__3, &l_Lean_Parser_Tactic_vcAlt___closed__3_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__3);
v___x_4085_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4086_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v___x_4084_);
lean_ctor_set(v___x_4086_, 2, v___x_4083_);
return v___x_4086_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__7(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4091_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__6));
v___x_4092_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__4, &l_Lean_Parser_Tactic_vcAlt___closed__4_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__4);
v___x_4093_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4094_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v___x_4092_);
lean_ctor_set(v___x_4094_, 2, v___x_4091_);
return v___x_4094_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt___closed__8(void){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4095_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__7, &l_Lean_Parser_Tactic_vcAlt___closed__7_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__7);
v___x_4096_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__1));
v___x_4097_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlt___closed__0));
v___x_4098_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
lean_ctor_set(v___x_4098_, 1, v___x_4096_);
lean_ctor_set(v___x_4098_, 2, v___x_4095_);
return v___x_4098_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlt(void){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlt___closed__8, &l_Lean_Parser_Tactic_vcAlt___closed__8_once, _init_l_Lean_Parser_Tactic_vcAlt___closed__8);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__10(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4126_ = l_Lean_Parser_Tactic_vcAlt;
v___x_4127_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__11));
v___x_4128_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4129_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v___x_4127_);
lean_ctor_set(v___x_4129_, 2, v___x_4126_);
return v___x_4129_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__11(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__10, &l_Lean_Parser_Tactic_vcAlts___closed__10_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__10);
v___x_4131_ = ((lean_object*)(l_Lean_Parser_Tactic_mspecialize___closed__5));
v___x_4132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v___x_4130_);
return v___x_4132_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__12(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4133_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__11, &l_Lean_Parser_Tactic_vcAlts___closed__11_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__11);
v___x_4134_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_4135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v___x_4133_);
return v___x_4135_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__13(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
v___x_4136_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__12, &l_Lean_Parser_Tactic_vcAlts___closed__12_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__12);
v___x_4137_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__9));
v___x_4138_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4139_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4138_);
lean_ctor_set(v___x_4139_, 1, v___x_4137_);
lean_ctor_set(v___x_4139_, 2, v___x_4136_);
return v___x_4139_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts___closed__14(void){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4140_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__13, &l_Lean_Parser_Tactic_vcAlts___closed__13_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__13);
v___x_4141_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__1));
v___x_4142_ = ((lean_object*)(l_Lean_Parser_Tactic_vcAlts___closed__0));
v___x_4143_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
lean_ctor_set(v___x_4143_, 1, v___x_4141_);
lean_ctor_set(v___x_4143_, 2, v___x_4140_);
return v___x_4143_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcAlts(void){
_start:
{
lean_object* v___x_4144_; 
v___x_4144_ = lean_obj_once(&l_Lean_Parser_Tactic_vcAlts___closed__14, &l_Lean_Parser_Tactic_vcAlts___closed__14_once, _init_l_Lean_Parser_Tactic_vcAlts___closed__14);
return v___x_4144_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__3(void){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4154_ = l_Lean_Parser_Tactic_optConfig;
v___x_4155_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__2));
v___x_4156_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4157_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4157_, 0, v___x_4156_);
lean_ctor_set(v___x_4157_, 1, v___x_4155_);
lean_ctor_set(v___x_4157_, 2, v___x_4154_);
return v___x_4157_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__8(void){
_start:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v___x_4164_ = l_Lean_Parser_Tactic_simpLemma;
v___x_4165_ = l_Lean_Parser_Tactic_simpErase;
v___x_4166_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4167_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v___x_4165_);
lean_ctor_set(v___x_4167_, 2, v___x_4164_);
return v___x_4167_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__9(void){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4168_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__8, &l_Lean_Parser_Tactic_mvcgen___closed__8_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__8);
v___x_4169_ = l_Lean_Parser_Tactic_simpStar;
v___x_4170_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantsKW___closed__3));
v___x_4171_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
lean_ctor_set(v___x_4171_, 1, v___x_4169_);
lean_ctor_set(v___x_4171_, 2, v___x_4168_);
return v___x_4171_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__10(void){
_start:
{
uint8_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4172_ = 1;
v___x_4173_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__5));
v___x_4174_ = ((lean_object*)(l_Lean_Parser_Tactic_mexists___closed__3));
v___x_4175_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__9, &l_Lean_Parser_Tactic_mvcgen___closed__9_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__9);
v___x_4176_ = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
lean_ctor_set(v___x_4176_, 1, v___x_4174_);
lean_ctor_set(v___x_4176_, 2, v___x_4173_);
lean_ctor_set_uint8(v___x_4176_, sizeof(void*)*3, v___x_4172_);
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__11(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__10, &l_Lean_Parser_Tactic_mvcgen___closed__10_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__10);
v___x_4178_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__7));
v___x_4179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
lean_ctor_set(v___x_4179_, 1, v___x_4177_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__12(void){
_start:
{
lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__11, &l_Lean_Parser_Tactic_mvcgen___closed__11_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__11);
v___x_4181_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__5));
v___x_4182_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4183_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
lean_ctor_set(v___x_4183_, 2, v___x_4180_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__15(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4187_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__14));
v___x_4188_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__12, &l_Lean_Parser_Tactic_mvcgen___closed__12_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__12);
v___x_4189_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4190_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
lean_ctor_set(v___x_4190_, 2, v___x_4187_);
return v___x_4190_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__16(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4191_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__15, &l_Lean_Parser_Tactic_mvcgen___closed__15_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__15);
v___x_4192_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___x_4191_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__17(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4194_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__16, &l_Lean_Parser_Tactic_mvcgen___closed__16_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__16);
v___x_4195_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__3, &l_Lean_Parser_Tactic_mvcgen___closed__3_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__3);
v___x_4196_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4197_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
lean_ctor_set(v___x_4197_, 1, v___x_4195_);
lean_ctor_set(v___x_4197_, 2, v___x_4194_);
return v___x_4197_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__18(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = l_Lean_Parser_Tactic_invariantAlts;
v___x_4199_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4199_);
lean_ctor_set(v___x_4200_, 1, v___x_4198_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__19(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4201_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__18, &l_Lean_Parser_Tactic_mvcgen___closed__18_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__18);
v___x_4202_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__17, &l_Lean_Parser_Tactic_mvcgen___closed__17_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__17);
v___x_4203_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4204_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
lean_ctor_set(v___x_4204_, 1, v___x_4202_);
lean_ctor_set(v___x_4204_, 2, v___x_4201_);
return v___x_4204_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__20(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v___x_4205_ = l_Lean_Parser_Tactic_vcAlts;
v___x_4206_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4207_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
lean_ctor_set(v___x_4207_, 1, v___x_4205_);
return v___x_4207_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__21(void){
_start:
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__20, &l_Lean_Parser_Tactic_mvcgen___closed__20_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__20);
v___x_4209_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__19, &l_Lean_Parser_Tactic_mvcgen___closed__19_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__19);
v___x_4210_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4211_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
lean_ctor_set(v___x_4211_, 1, v___x_4209_);
lean_ctor_set(v___x_4211_, 2, v___x_4208_);
return v___x_4211_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen___closed__22(void){
_start:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4212_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__21, &l_Lean_Parser_Tactic_mvcgen___closed__21_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__21);
v___x_4213_ = lean_unsigned_to_nat(1022u);
v___x_4214_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgen___closed__1));
v___x_4215_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
lean_ctor_set(v___x_4215_, 1, v___x_4213_);
lean_ctor_set(v___x_4215_, 2, v___x_4212_);
return v___x_4215_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgen(void){
_start:
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__22, &l_Lean_Parser_Tactic_mvcgen___closed__22_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__22);
return v___x_4216_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4(void){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4227_ = l_Lean_Parser_Tactic_optConfig;
v___x_4228_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__3));
v___x_4229_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4230_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4229_);
lean_ctor_set(v___x_4230_, 1, v___x_4228_);
lean_ctor_set(v___x_4230_, 2, v___x_4227_);
return v___x_4230_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4231_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__16, &l_Lean_Parser_Tactic_mvcgen___closed__16_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__16);
v___x_4232_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__4, &l_Lean_Parser_Tactic_mvcgenHint___closed__4_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__4);
v___x_4233_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4234_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
lean_ctor_set(v___x_4234_, 1, v___x_4232_);
lean_ctor_set(v___x_4234_, 2, v___x_4231_);
return v___x_4234_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4235_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__5, &l_Lean_Parser_Tactic_mvcgenHint___closed__5_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__5);
v___x_4236_ = lean_unsigned_to_nat(1022u);
v___x_4237_ = ((lean_object*)(l_Lean_Parser_Tactic_mvcgenHint___closed__1));
v___x_4238_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
lean_ctor_set(v___x_4238_, 1, v___x_4236_);
lean_ctor_set(v___x_4238_, 2, v___x_4235_);
return v___x_4238_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_mvcgenHint(void){
_start:
{
lean_object* v___x_4239_; 
v___x_4239_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgenHint___closed__6, &l_Lean_Parser_Tactic_mvcgenHint___closed__6_once, _init_l_Lean_Parser_Tactic_mvcgenHint___closed__6);
return v___x_4239_;
}
}
static lean_object* _init_l_Lean_Parser_Category_vcgenDischarge(void){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_box(0);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__3(void){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4307_ = l_Lean_Parser_Tactic_optConfig;
v___x_4308_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__2));
v___x_4309_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4310_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
lean_ctor_set(v___x_4310_, 1, v___x_4308_);
lean_ctor_set(v___x_4310_, 2, v___x_4307_);
return v___x_4310_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__4(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4311_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__16, &l_Lean_Parser_Tactic_mvcgen___closed__16_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__16);
v___x_4312_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__3, &l_Lean_Parser_Tactic_vcgen___closed__3_once, _init_l_Lean_Parser_Tactic_vcgen___closed__3);
v___x_4313_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4314_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4313_);
lean_ctor_set(v___x_4314_, 1, v___x_4312_);
lean_ctor_set(v___x_4314_, 2, v___x_4311_);
return v___x_4314_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__9(void){
_start:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4326_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__8));
v___x_4327_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__4, &l_Lean_Parser_Tactic_vcgen___closed__4_once, _init_l_Lean_Parser_Tactic_vcgen___closed__4);
v___x_4328_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4329_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4328_);
lean_ctor_set(v___x_4329_, 1, v___x_4327_);
lean_ctor_set(v___x_4329_, 2, v___x_4326_);
return v___x_4329_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__12(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4334_ = l_Lean_Parser_Tactic_frameAlt;
v___x_4335_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantDotAlt___closed__11));
v___x_4336_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4337_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4336_);
lean_ctor_set(v___x_4337_, 1, v___x_4335_);
lean_ctor_set(v___x_4337_, 2, v___x_4334_);
return v___x_4337_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__13(void){
_start:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__12, &l_Lean_Parser_Tactic_vcgen___closed__12_once, _init_l_Lean_Parser_Tactic_vcgen___closed__12);
v___x_4339_ = ((lean_object*)(l_Lean_Parser_Tactic_mrenameI___closed__5));
v___x_4340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
lean_ctor_set(v___x_4340_, 1, v___x_4338_);
return v___x_4340_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__14(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__13, &l_Lean_Parser_Tactic_vcgen___closed__13_once, _init_l_Lean_Parser_Tactic_vcgen___closed__13);
v___x_4342_ = ((lean_object*)(l_Lean_Parser_Tactic_invariantAlts___closed__3));
v___x_4343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
lean_ctor_set(v___x_4343_, 1, v___x_4341_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__15(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4344_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__14, &l_Lean_Parser_Tactic_vcgen___closed__14_once, _init_l_Lean_Parser_Tactic_vcgen___closed__14);
v___x_4345_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__11));
v___x_4346_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4347_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v___x_4345_);
lean_ctor_set(v___x_4347_, 2, v___x_4344_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__16(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__15, &l_Lean_Parser_Tactic_vcgen___closed__15_once, _init_l_Lean_Parser_Tactic_vcgen___closed__15);
v___x_4349_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__9));
v___x_4350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v___x_4348_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__17(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4351_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__16, &l_Lean_Parser_Tactic_vcgen___closed__16_once, _init_l_Lean_Parser_Tactic_vcgen___closed__16);
v___x_4352_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__9, &l_Lean_Parser_Tactic_vcgen___closed__9_once, _init_l_Lean_Parser_Tactic_vcgen___closed__9);
v___x_4353_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4354_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4354_, 0, v___x_4353_);
lean_ctor_set(v___x_4354_, 1, v___x_4352_);
lean_ctor_set(v___x_4354_, 2, v___x_4351_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__18(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4355_ = lean_obj_once(&l_Lean_Parser_Tactic_mvcgen___closed__18, &l_Lean_Parser_Tactic_mvcgen___closed__18_once, _init_l_Lean_Parser_Tactic_mvcgen___closed__18);
v___x_4356_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__17, &l_Lean_Parser_Tactic_vcgen___closed__17_once, _init_l_Lean_Parser_Tactic_vcgen___closed__17);
v___x_4357_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4358_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
lean_ctor_set(v___x_4358_, 1, v___x_4356_);
lean_ctor_set(v___x_4358_, 2, v___x_4355_);
return v___x_4358_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__31(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4399_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__30));
v___x_4400_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__18, &l_Lean_Parser_Tactic_vcgen___closed__18_once, _init_l_Lean_Parser_Tactic_vcgen___closed__18);
v___x_4401_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4402_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4401_);
lean_ctor_set(v___x_4402_, 1, v___x_4400_);
lean_ctor_set(v___x_4402_, 2, v___x_4399_);
return v___x_4402_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__35(void){
_start:
{
lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4413_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__34));
v___x_4414_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__31, &l_Lean_Parser_Tactic_vcgen___closed__31_once, _init_l_Lean_Parser_Tactic_vcgen___closed__31);
v___x_4415_ = ((lean_object*)(l_Lean_Parser_Attr_spec___closed__6));
v___x_4416_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_4416_, 0, v___x_4415_);
lean_ctor_set(v___x_4416_, 1, v___x_4414_);
lean_ctor_set(v___x_4416_, 2, v___x_4413_);
return v___x_4416_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen___closed__36(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4417_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__35, &l_Lean_Parser_Tactic_vcgen___closed__35_once, _init_l_Lean_Parser_Tactic_vcgen___closed__35);
v___x_4418_ = lean_unsigned_to_nat(1022u);
v___x_4419_ = ((lean_object*)(l_Lean_Parser_Tactic_vcgen___closed__1));
v___x_4420_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4419_);
lean_ctor_set(v___x_4420_, 1, v___x_4418_);
lean_ctor_set(v___x_4420_, 2, v___x_4417_);
return v___x_4420_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_vcgen(void){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__36, &l_Lean_Parser_Tactic_vcgen___closed__36_once, _init_l_Lean_Parser_Tactic_vcgen___closed__36);
return v___x_4421_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_vcgen___closed__2(void){
_start:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4429_ = lean_obj_once(&l_Lean_Parser_Tactic_vcgen___closed__31, &l_Lean_Parser_Tactic_vcgen___closed__31_once, _init_l_Lean_Parser_Tactic_vcgen___closed__31);
v___x_4430_ = lean_unsigned_to_nat(1022u);
v___x_4431_ = ((lean_object*)(l_Lean_Parser_Tactic_Grind_vcgen___closed__1));
v___x_4432_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4431_);
lean_ctor_set(v___x_4432_, 1, v___x_4430_);
lean_ctor_set(v___x_4432_, 2, v___x_4429_);
return v___x_4432_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Grind_vcgen(void){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = lean_obj_once(&l_Lean_Parser_Tactic_Grind_vcgen___closed__2, &l_Lean_Parser_Tactic_Grind_vcgen___closed__2_once, _init_l_Lean_Parser_Tactic_Grind_vcgen___closed__2);
return v___x_4433_;
}
}
lean_object* runtime_initialize_Std_Do(uint8_t builtin);
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
l_Lean_Parser_Tactic_invariantDotAlt = _init_l_Lean_Parser_Tactic_invariantDotAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantDotAlt);
l_Lean_Parser_Tactic_invariantCaseAlt = _init_l_Lean_Parser_Tactic_invariantCaseAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantCaseAlt);
l_Lean_Parser_Tactic_invariantAlts = _init_l_Lean_Parser_Tactic_invariantAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_invariantAlts);
l_Lean_Parser_Tactic_frameAlt = _init_l_Lean_Parser_Tactic_frameAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_frameAlt);
l_Lean_Parser_Tactic_vcAlt = _init_l_Lean_Parser_Tactic_vcAlt();
lean_mark_persistent(l_Lean_Parser_Tactic_vcAlt);
l_Lean_Parser_Tactic_vcAlts = _init_l_Lean_Parser_Tactic_vcAlts();
lean_mark_persistent(l_Lean_Parser_Tactic_vcAlts);
l_Lean_Parser_Tactic_mvcgen = _init_l_Lean_Parser_Tactic_mvcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_mvcgen);
l_Lean_Parser_Tactic_mvcgenHint = _init_l_Lean_Parser_Tactic_mvcgenHint();
lean_mark_persistent(l_Lean_Parser_Tactic_mvcgenHint);
l_Lean_Parser_Category_vcgenDischarge = _init_l_Lean_Parser_Category_vcgenDischarge();
lean_mark_persistent(l_Lean_Parser_Category_vcgenDischarge);
l_Lean_Parser_Tactic_vcgen = _init_l_Lean_Parser_Tactic_vcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_vcgen);
l_Lean_Parser_Tactic_Grind_vcgen = _init_l_Lean_Parser_Tactic_Grind_vcgen();
lean_mark_persistent(l_Lean_Parser_Tactic_Grind_vcgen);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do(uint8_t builtin);
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
