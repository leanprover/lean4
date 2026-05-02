// Lean compiler output
// Module: Init.NotationExtra
// Imports: public import Init.Conv public import Init.GetElem import Init.Meta.Defs
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_binderIdent;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Macro_throwError___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unbracketedExplicitBinders"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__0 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__0_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__1 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__2_value_aux_0),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 220, 119, 82, 242, 112, 119, 200)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__2 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__2_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__3 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__3_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__4 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__5 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__5_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__5_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__6 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__6_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ppSpace"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__7 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__7_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__7_value),LEAN_SCALAR_PTR_LITERAL(207, 47, 58, 43, 30, 240, 125, 246)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__8 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__8_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__8_value)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__9 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__9_value;
static lean_once_cell_t l_Lean_unbracketedExplicitBinders___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_unbracketedExplicitBinders___closed__10;
static lean_once_cell_t l_Lean_unbracketedExplicitBinders___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_unbracketedExplicitBinders___closed__11;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__12 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__12_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__12_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__13 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__14 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__14_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__14_value)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__15 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__15_value;
static const lean_string_object l_Lean_unbracketedExplicitBinders___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__16 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__16_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__16_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__17 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__17_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__18 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__15_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__19 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__19_value;
static const lean_ctor_object l_Lean_unbracketedExplicitBinders___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__19_value)}};
static const lean_object* l_Lean_unbracketedExplicitBinders___closed__20 = (const lean_object*)&l_Lean_unbracketedExplicitBinders___closed__20_value;
static lean_once_cell_t l_Lean_unbracketedExplicitBinders___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_unbracketedExplicitBinders___closed__21;
static lean_once_cell_t l_Lean_unbracketedExplicitBinders___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_unbracketedExplicitBinders___closed__22;
LEAN_EXPORT lean_object* l_Lean_unbracketedExplicitBinders;
static const lean_string_object l_Lean_bracketedExplicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "bracketedExplicitBinders"};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__0 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__0_value;
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_bracketedExplicitBinders___closed__1_value_aux_0),((lean_object*)&l_Lean_bracketedExplicitBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 65, 7, 186, 44, 89, 152, 79)}};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__1 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__1_value;
static const lean_string_object l_Lean_bracketedExplicitBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__2 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__2_value;
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_bracketedExplicitBinders___closed__2_value)}};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__3 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__3_value;
static const lean_string_object l_Lean_bracketedExplicitBinders___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "withoutPosition"};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__4 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__4_value;
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_bracketedExplicitBinders___closed__4_value),LEAN_SCALAR_PTR_LITERAL(69, 6, 27, 142, 141, 165, 41, 16)}};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__5 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__5_value;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__6;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__7;
static const lean_string_object l_Lean_bracketedExplicitBinders___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__8 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__8_value;
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_bracketedExplicitBinders___closed__8_value)}};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__9 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__9_value;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__10;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__11;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__12;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__13;
static const lean_string_object l_Lean_bracketedExplicitBinders___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__14 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__14_value;
static const lean_ctor_object l_Lean_bracketedExplicitBinders___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_bracketedExplicitBinders___closed__14_value)}};
static const lean_object* l_Lean_bracketedExplicitBinders___closed__15 = (const lean_object*)&l_Lean_bracketedExplicitBinders___closed__15_value;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__16;
static lean_once_cell_t l_Lean_bracketedExplicitBinders___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_bracketedExplicitBinders___closed__17;
LEAN_EXPORT lean_object* l_Lean_bracketedExplicitBinders;
static const lean_string_object l_Lean_explicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Lean_explicitBinders___closed__0 = (const lean_object*)&l_Lean_explicitBinders___closed__0_value;
static const lean_ctor_object l_Lean_explicitBinders___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_explicitBinders___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_explicitBinders___closed__1_value_aux_0),((lean_object*)&l_Lean_explicitBinders___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
static const lean_object* l_Lean_explicitBinders___closed__1 = (const lean_object*)&l_Lean_explicitBinders___closed__1_value;
static const lean_string_object l_Lean_explicitBinders___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "orelse"};
static const lean_object* l_Lean_explicitBinders___closed__2 = (const lean_object*)&l_Lean_explicitBinders___closed__2_value;
static const lean_ctor_object l_Lean_explicitBinders___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_explicitBinders___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 76, 4, 51, 251, 212, 116, 5)}};
static const lean_object* l_Lean_explicitBinders___closed__3 = (const lean_object*)&l_Lean_explicitBinders___closed__3_value;
static lean_once_cell_t l_Lean_explicitBinders___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_explicitBinders___closed__4;
static lean_once_cell_t l_Lean_explicitBinders___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_explicitBinders___closed__5;
static lean_once_cell_t l_Lean_explicitBinders___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_explicitBinders___closed__6;
static lean_once_cell_t l_Lean_explicitBinders___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_explicitBinders___closed__7;
LEAN_EXPORT lean_object* l_Lean_explicitBinders;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__2 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value_aux_2),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__4 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__4_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value_aux_2),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__8 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__8_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value_aux_2),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12_value;
static lean_once_cell_t l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15_value;
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value_aux_2),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16_value;
static const lean_string_object l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17 = (const lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExplicitBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExplicitBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandBracketedBindersAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandBracketedBindersAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_expandExplicitBinders___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected explicit binder"};
static const lean_object* l_Lean_expandExplicitBinders___closed__0 = (const lean_object*)&l_Lean_expandExplicitBinders___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_unifConstraint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "unifConstraint"};
static const lean_object* l_Lean_unifConstraint___closed__0 = (const lean_object*)&l_Lean_unifConstraint___closed__0_value;
static const lean_ctor_object l_Lean_unifConstraint___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_unifConstraint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unifConstraint___closed__1_value_aux_0),((lean_object*)&l_Lean_unifConstraint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 40, 39, 182, 219, 40, 214, 56)}};
static const lean_object* l_Lean_unifConstraint___closed__1 = (const lean_object*)&l_Lean_unifConstraint___closed__1_value;
static const lean_string_object l_Lean_unifConstraint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ≟ "};
static const lean_object* l_Lean_unifConstraint___closed__2 = (const lean_object*)&l_Lean_unifConstraint___closed__2_value;
static const lean_string_object l_Lean_unifConstraint___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l_Lean_unifConstraint___closed__3 = (const lean_object*)&l_Lean_unifConstraint___closed__3_value;
static const lean_ctor_object l_Lean_unifConstraint___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean_unifConstraint___closed__2_value),((lean_object*)&l_Lean_unifConstraint___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_unifConstraint___closed__4 = (const lean_object*)&l_Lean_unifConstraint___closed__4_value;
static const lean_ctor_object l_Lean_unifConstraint___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value),((lean_object*)&l_Lean_unifConstraint___closed__4_value)}};
static const lean_object* l_Lean_unifConstraint___closed__5 = (const lean_object*)&l_Lean_unifConstraint___closed__5_value;
static const lean_ctor_object l_Lean_unifConstraint___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unifConstraint___closed__5_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_unifConstraint___closed__6 = (const lean_object*)&l_Lean_unifConstraint___closed__6_value;
static const lean_ctor_object l_Lean_unifConstraint___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_unifConstraint___closed__0_value),((lean_object*)&l_Lean_unifConstraint___closed__1_value),((lean_object*)&l_Lean_unifConstraint___closed__6_value)}};
static const lean_object* l_Lean_unifConstraint___closed__7 = (const lean_object*)&l_Lean_unifConstraint___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_unifConstraint = (const lean_object*)&l_Lean_unifConstraint___closed__7_value;
static const lean_string_object l_Lean_unifConstraintElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unifConstraintElem"};
static const lean_object* l_Lean_unifConstraintElem___closed__0 = (const lean_object*)&l_Lean_unifConstraintElem___closed__0_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_unifConstraintElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unifConstraintElem___closed__1_value_aux_0),((lean_object*)&l_Lean_unifConstraintElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 160, 61, 144, 137, 134, 194, 47)}};
static const lean_object* l_Lean_unifConstraintElem___closed__1 = (const lean_object*)&l_Lean_unifConstraintElem___closed__1_value;
static const lean_string_object l_Lean_unifConstraintElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGe"};
static const lean_object* l_Lean_unifConstraintElem___closed__2 = (const lean_object*)&l_Lean_unifConstraintElem___closed__2_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unifConstraintElem___closed__2_value),LEAN_SCALAR_PTR_LITERAL(119, 36, 80, 74, 173, 106, 150, 68)}};
static const lean_object* l_Lean_unifConstraintElem___closed__3 = (const lean_object*)&l_Lean_unifConstraintElem___closed__3_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_unifConstraintElem___closed__3_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__4 = (const lean_object*)&l_Lean_unifConstraintElem___closed__4_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unifConstraintElem___closed__4_value),((lean_object*)&l_Lean_unifConstraint___closed__7_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__5 = (const lean_object*)&l_Lean_unifConstraintElem___closed__5_value;
static const lean_string_object l_Lean_unifConstraintElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_unifConstraintElem___closed__6 = (const lean_object*)&l_Lean_unifConstraintElem___closed__6_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_unifConstraintElem___closed__6_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__7 = (const lean_object*)&l_Lean_unifConstraintElem___closed__7_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_unifConstraintElem___closed__7_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__8 = (const lean_object*)&l_Lean_unifConstraintElem___closed__8_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unifConstraintElem___closed__5_value),((lean_object*)&l_Lean_unifConstraintElem___closed__8_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__9 = (const lean_object*)&l_Lean_unifConstraintElem___closed__9_value;
static const lean_ctor_object l_Lean_unifConstraintElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_unifConstraintElem___closed__0_value),((lean_object*)&l_Lean_unifConstraintElem___closed__1_value),((lean_object*)&l_Lean_unifConstraintElem___closed__9_value)}};
static const lean_object* l_Lean_unifConstraintElem___closed__10 = (const lean_object*)&l_Lean_unifConstraintElem___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_unifConstraintElem = (const lean_object*)&l_Lean_unifConstraintElem___closed__10_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 34, .m_data = "command__Unif_hint____Where_|_-⊢__"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__0 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__0_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1_value_aux_0),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 81, 240, 79, 209, 199, 153, 255)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__2 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__2_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(229, 56, 215, 222, 243, 187, 251, 54)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__3 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__3_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__3_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__4 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__4_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__4_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__5 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__5_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(144, 113, 220, 36, 163, 13, 57, 223)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__7 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__7_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__7_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__8 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__8_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__5_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__8_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__9 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__9_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unif_hint"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__10 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__10_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__10_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__11 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__11_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__9_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__11_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__12 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__12_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__13 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__13_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__13_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__15 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__15_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__9_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__15_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__16 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__16_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__16_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__17 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__17_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__12_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__17_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__18 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__18_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__19 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__19_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__19_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bracketedBinder"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__21 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__21_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__21_value),LEAN_SCALAR_PTR_LITERAL(126, 188, 9, 177, 18, 110, 216, 30)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__22 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__22_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__22_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__23 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__23_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__9_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__23_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__24 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__24_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__24_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__25 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__25_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__18_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__25_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__26 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__26_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " where "};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__27 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__27_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__27_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__28 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__28_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__26_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__28_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__29 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__29_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "withPosition"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__30 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__30_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__30_value),LEAN_SCALAR_PTR_LITERAL(246, 171, 180, 145, 132, 143, 108, 238)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_Lean_unifConstraintElem___closed__10_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__32 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__32_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__32_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__33 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__33_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__29_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__33_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__34 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__34_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "patternIgnore"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__35 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__35_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__35_value),LEAN_SCALAR_PTR_LITERAL(195, 83, 213, 191, 208, 4, 123, 240)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__36 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__36_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__37 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__37_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__37_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "atomic"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__39 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__39_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__39_value),LEAN_SCALAR_PTR_LITERAL(56, 145, 113, 208, 127, 167, 216, 55)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__40 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__40_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__42 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__42_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noWs"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__43 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__43_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__43_value),LEAN_SCALAR_PTR_LITERAL(92, 29, 204, 148, 167, 109, 242, 21)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__44 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__44_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__44_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__45 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__45_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__42_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__45_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__46 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__46_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__47 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__47_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__47_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__48 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__48_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__46_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__48_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__49 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__49_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__40_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__49_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__50 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__50_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__50_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__51 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__51_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⊢"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52_value;
static const lean_string_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__53 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__53_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__53_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54_value_aux_0),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52_value),LEAN_SCALAR_PTR_LITERAL(140, 188, 44, 162, 35, 62, 206, 40)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__55 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__55_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__52_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__54_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__55_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__56 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__56_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_explicitBinders___closed__3_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__51_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__56_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__57 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__57_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__36_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__57_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__58 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__58_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__34_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__58_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__59 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__59_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__59_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__9_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__60 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__60_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__60_value),((lean_object*)&l_Lean_unifConstraint___closed__7_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__61 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__61_value;
static const lean_ctor_object l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__61_value)}};
static const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__62 = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__62_value;
LEAN_EXPORT const lean_object* l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2____ = (const lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__62_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arrow"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(182, 146, 143, 73, 122, 115, 5, 207)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "→"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sort"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Sort"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Level"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unification_hint"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(169, 153, 150, 74, 163, 227, 238, 154)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "expose"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(170, 113, 233, 77, 243, 78, 243, 129)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hint"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(166, 129, 8, 98, 135, 223, 96, 106)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32_value;
static const lean_array_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value_aux_2),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value_aux_2),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_u2203___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 8, .m_data = "term∃_,_"};
static const lean_object* l_term_u2203___x2c___00__closed__0 = (const lean_object*)&l_term_u2203___x2c___00__closed__0_value;
static const lean_ctor_object l_term_u2203___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_u2203___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 105, 219, 112, 166, 139, 167, 161)}};
static const lean_object* l_term_u2203___x2c___00__closed__1 = (const lean_object*)&l_term_u2203___x2c___00__closed__1_value;
static const lean_string_object l_term_u2203___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "∃"};
static const lean_object* l_term_u2203___x2c___00__closed__2 = (const lean_object*)&l_term_u2203___x2c___00__closed__2_value;
static const lean_ctor_object l_term_u2203___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_u2203___x2c___00__closed__2_value)}};
static const lean_object* l_term_u2203___x2c___00__closed__3 = (const lean_object*)&l_term_u2203___x2c___00__closed__3_value;
static lean_once_cell_t l_term_u2203___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u2203___x2c___00__closed__4;
static lean_once_cell_t l_term_u2203___x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u2203___x2c___00__closed__5;
static lean_once_cell_t l_term_u2203___x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u2203___x2c___00__closed__6;
static lean_once_cell_t l_term_u2203___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u2203___x2c___00__closed__7;
LEAN_EXPORT lean_object* l_term_u2203___x2c__;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_termExists___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "termExists_,_"};
static const lean_object* l_termExists___x2c___00__closed__0 = (const lean_object*)&l_termExists___x2c___00__closed__0_value;
static const lean_ctor_object l_termExists___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termExists___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 28, 246, 22, 86, 216, 86, 26)}};
static const lean_object* l_termExists___x2c___00__closed__1 = (const lean_object*)&l_termExists___x2c___00__closed__1_value;
static const lean_string_object l_termExists___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_termExists___x2c___00__closed__2 = (const lean_object*)&l_termExists___x2c___00__closed__2_value;
static const lean_ctor_object l_termExists___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_termExists___x2c___00__closed__2_value)}};
static const lean_object* l_termExists___x2c___00__closed__3 = (const lean_object*)&l_termExists___x2c___00__closed__3_value;
static lean_once_cell_t l_termExists___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_termExists___x2c___00__closed__4;
static lean_once_cell_t l_termExists___x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_termExists___x2c___00__closed__5;
static lean_once_cell_t l_termExists___x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_termExists___x2c___00__closed__6;
static lean_once_cell_t l_termExists___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_termExists___x2c___00__closed__7;
LEAN_EXPORT lean_object* l_termExists___x2c__;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_u03a3___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 8, .m_data = "termΣ_,_"};
static const lean_object* l_term_u03a3___x2c___00__closed__0 = (const lean_object*)&l_term_u03a3___x2c___00__closed__0_value;
static const lean_ctor_object l_term_u03a3___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_u03a3___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 61, 86, 48, 13, 47, 85, 120)}};
static const lean_object* l_term_u03a3___x2c___00__closed__1 = (const lean_object*)&l_term_u03a3___x2c___00__closed__1_value;
static const lean_string_object l_term_u03a3___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "Σ"};
static const lean_object* l_term_u03a3___x2c___00__closed__2 = (const lean_object*)&l_term_u03a3___x2c___00__closed__2_value;
static const lean_ctor_object l_term_u03a3___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_u03a3___x2c___00__closed__2_value)}};
static const lean_object* l_term_u03a3___x2c___00__closed__3 = (const lean_object*)&l_term_u03a3___x2c___00__closed__3_value;
static lean_once_cell_t l_term_u03a3___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3___x2c___00__closed__4;
static lean_once_cell_t l_term_u03a3___x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3___x2c___00__closed__5;
static lean_once_cell_t l_term_u03a3___x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3___x2c___00__closed__6;
static lean_once_cell_t l_term_u03a3___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3___x2c___00__closed__7;
LEAN_EXPORT lean_object* l_term_u03a3___x2c__;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Sigma"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 250, 144, 56, 109, 24, 162, 237)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_u03a3_x27___x2c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 9, .m_data = "termΣ'_,_"};
static const lean_object* l_term_u03a3_x27___x2c___00__closed__0 = (const lean_object*)&l_term_u03a3_x27___x2c___00__closed__0_value;
static const lean_ctor_object l_term_u03a3_x27___x2c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_u03a3_x27___x2c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 244, 129, 9, 43, 224, 237, 22)}};
static const lean_object* l_term_u03a3_x27___x2c___00__closed__1 = (const lean_object*)&l_term_u03a3_x27___x2c___00__closed__1_value;
static const lean_string_object l_term_u03a3_x27___x2c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "Σ'"};
static const lean_object* l_term_u03a3_x27___x2c___00__closed__2 = (const lean_object*)&l_term_u03a3_x27___x2c___00__closed__2_value;
static const lean_ctor_object l_term_u03a3_x27___x2c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term_u03a3_x27___x2c___00__closed__2_value)}};
static const lean_object* l_term_u03a3_x27___x2c___00__closed__3 = (const lean_object*)&l_term_u03a3_x27___x2c___00__closed__3_value;
static lean_once_cell_t l_term_u03a3_x27___x2c___00__closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3_x27___x2c___00__closed__4;
static lean_once_cell_t l_term_u03a3_x27___x2c___00__closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3_x27___x2c___00__closed__5;
static lean_once_cell_t l_term_u03a3_x27___x2c___00__closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3_x27___x2c___00__closed__6;
static lean_once_cell_t l_term_u03a3_x27___x2c___00__closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term_u03a3_x27___x2c___00__closed__7;
LEAN_EXPORT lean_object* l_term_u03a3_x27___x2c__;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "PSigma"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 171, 149, 177, 120, 131, 37, 223)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___xd7____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 9, .m_data = "term_×__1"};
static const lean_object* l_term___xd7____1___closed__0 = (const lean_object*)&l_term___xd7____1___closed__0_value;
static const lean_ctor_object l_term___xd7____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___xd7____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 66, 226, 190, 84, 185, 148, 180)}};
static const lean_object* l_term___xd7____1___closed__1 = (const lean_object*)&l_term___xd7____1___closed__1_value;
static const lean_string_object l_term___xd7____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 3, .m_data = " × "};
static const lean_object* l_term___xd7____1___closed__2 = (const lean_object*)&l_term___xd7____1___closed__2_value;
static const lean_ctor_object l_term___xd7____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___xd7____1___closed__2_value)}};
static const lean_object* l_term___xd7____1___closed__3 = (const lean_object*)&l_term___xd7____1___closed__3_value;
static lean_once_cell_t l_term___xd7____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7____1___closed__4;
static const lean_ctor_object l_term___xd7____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__17_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_term___xd7____1___closed__5 = (const lean_object*)&l_term___xd7____1___closed__5_value;
static lean_once_cell_t l_term___xd7____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7____1___closed__6;
static lean_once_cell_t l_term___xd7____1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7____1___closed__7;
LEAN_EXPORT lean_object* l_term___xd7____1;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___xd7_x27____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 10, .m_data = "term_×'__1"};
static const lean_object* l_term___xd7_x27____1___closed__0 = (const lean_object*)&l_term___xd7_x27____1___closed__0_value;
static const lean_ctor_object l_term___xd7_x27____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___xd7_x27____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(107, 58, 119, 129, 26, 229, 143, 92)}};
static const lean_object* l_term___xd7_x27____1___closed__1 = (const lean_object*)&l_term___xd7_x27____1___closed__1_value;
static const lean_string_object l_term___xd7_x27____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 4, .m_data = " ×' "};
static const lean_object* l_term___xd7_x27____1___closed__2 = (const lean_object*)&l_term___xd7_x27____1___closed__2_value;
static const lean_ctor_object l_term___xd7_x27____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___xd7_x27____1___closed__2_value)}};
static const lean_object* l_term___xd7_x27____1___closed__3 = (const lean_object*)&l_term___xd7_x27____1___closed__3_value;
static lean_once_cell_t l_term___xd7_x27____1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7_x27____1___closed__4;
static lean_once_cell_t l_term___xd7_x27____1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7_x27____1___closed__5;
static lean_once_cell_t l_term___xd7_x27____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_term___xd7_x27____1___closed__6;
LEAN_EXPORT lean_object* l_term___xd7_x27____1;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_calcFirstStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "calcFirstStep"};
static const lean_object* l_Lean_calcFirstStep___closed__0 = (const lean_object*)&l_Lean_calcFirstStep___closed__0_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_calcFirstStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcFirstStep___closed__1_value_aux_0),((lean_object*)&l_Lean_calcFirstStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 79, 246, 49, 58, 153, 94, 105)}};
static const lean_object* l_Lean_calcFirstStep___closed__1 = (const lean_object*)&l_Lean_calcFirstStep___closed__1_value;
static const lean_string_object l_Lean_calcFirstStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppIndent"};
static const lean_object* l_Lean_calcFirstStep___closed__2 = (const lean_object*)&l_Lean_calcFirstStep___closed__2_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_calcFirstStep___closed__2_value),LEAN_SCALAR_PTR_LITERAL(240, 142, 232, 190, 100, 212, 29, 41)}};
static const lean_object* l_Lean_calcFirstStep___closed__3 = (const lean_object*)&l_Lean_calcFirstStep___closed__3_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unifConstraintElem___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__4 = (const lean_object*)&l_Lean_calcFirstStep___closed__4_value;
static const lean_string_object l_Lean_calcFirstStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_calcFirstStep___closed__5 = (const lean_object*)&l_Lean_calcFirstStep___closed__5_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_calcFirstStep___closed__5_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__6 = (const lean_object*)&l_Lean_calcFirstStep___closed__6_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__6_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__7 = (const lean_object*)&l_Lean_calcFirstStep___closed__7_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_calcFirstStep___closed__7_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__8 = (const lean_object*)&l_Lean_calcFirstStep___closed__8_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__8_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__9 = (const lean_object*)&l_Lean_calcFirstStep___closed__9_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcFirstStep___closed__3_value),((lean_object*)&l_Lean_calcFirstStep___closed__9_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__10 = (const lean_object*)&l_Lean_calcFirstStep___closed__10_value;
static const lean_ctor_object l_Lean_calcFirstStep___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_calcFirstStep___closed__0_value),((lean_object*)&l_Lean_calcFirstStep___closed__1_value),((lean_object*)&l_Lean_calcFirstStep___closed__10_value)}};
static const lean_object* l_Lean_calcFirstStep___closed__11 = (const lean_object*)&l_Lean_calcFirstStep___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_calcFirstStep = (const lean_object*)&l_Lean_calcFirstStep___closed__11_value;
static const lean_string_object l_Lean_calcStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "calcStep"};
static const lean_object* l_Lean_calcStep___closed__0 = (const lean_object*)&l_Lean_calcStep___closed__0_value;
static const lean_ctor_object l_Lean_calcStep___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_calcStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcStep___closed__1_value_aux_0),((lean_object*)&l_Lean_calcStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 3, 210, 123, 188, 211, 75, 180)}};
static const lean_object* l_Lean_calcStep___closed__1 = (const lean_object*)&l_Lean_calcStep___closed__1_value;
static const lean_ctor_object l_Lean_calcStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__6_value)}};
static const lean_object* l_Lean_calcStep___closed__2 = (const lean_object*)&l_Lean_calcStep___closed__2_value;
static const lean_ctor_object l_Lean_calcStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcStep___closed__2_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_calcStep___closed__3 = (const lean_object*)&l_Lean_calcStep___closed__3_value;
static const lean_ctor_object l_Lean_calcStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcFirstStep___closed__3_value),((lean_object*)&l_Lean_calcStep___closed__3_value)}};
static const lean_object* l_Lean_calcStep___closed__4 = (const lean_object*)&l_Lean_calcStep___closed__4_value;
static const lean_ctor_object l_Lean_calcStep___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_calcStep___closed__0_value),((lean_object*)&l_Lean_calcStep___closed__1_value),((lean_object*)&l_Lean_calcStep___closed__4_value)}};
static const lean_object* l_Lean_calcStep___closed__5 = (const lean_object*)&l_Lean_calcStep___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_calcStep = (const lean_object*)&l_Lean_calcStep___closed__5_value;
static const lean_string_object l_Lean_calcSteps___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "calcSteps"};
static const lean_object* l_Lean_calcSteps___closed__0 = (const lean_object*)&l_Lean_calcSteps___closed__0_value;
static const lean_ctor_object l_Lean_calcSteps___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_calcSteps___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcSteps___closed__1_value_aux_0),((lean_object*)&l_Lean_calcSteps___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 10, 254, 10, 206, 238, 242, 161)}};
static const lean_object* l_Lean_calcSteps___closed__1 = (const lean_object*)&l_Lean_calcSteps___closed__1_value;
static const lean_string_object l_Lean_calcSteps___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_calcSteps___closed__2 = (const lean_object*)&l_Lean_calcSteps___closed__2_value;
static const lean_ctor_object l_Lean_calcSteps___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_calcSteps___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_calcSteps___closed__3 = (const lean_object*)&l_Lean_calcSteps___closed__3_value;
static const lean_ctor_object l_Lean_calcSteps___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_calcSteps___closed__3_value)}};
static const lean_object* l_Lean_calcSteps___closed__4 = (const lean_object*)&l_Lean_calcSteps___closed__4_value;
static const lean_ctor_object l_Lean_calcSteps___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_calcFirstStep___closed__11_value)}};
static const lean_object* l_Lean_calcSteps___closed__5 = (const lean_object*)&l_Lean_calcSteps___closed__5_value;
static const lean_ctor_object l_Lean_calcSteps___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__5_value)}};
static const lean_object* l_Lean_calcSteps___closed__6 = (const lean_object*)&l_Lean_calcSteps___closed__6_value;
static const lean_string_object l_Lean_calcSteps___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l_Lean_calcSteps___closed__7 = (const lean_object*)&l_Lean_calcSteps___closed__7_value;
static const lean_ctor_object l_Lean_calcSteps___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_calcSteps___closed__7_value),LEAN_SCALAR_PTR_LITERAL(74, 147, 100, 44, 136, 108, 159, 66)}};
static const lean_object* l_Lean_calcSteps___closed__8 = (const lean_object*)&l_Lean_calcSteps___closed__8_value;
static const lean_ctor_object l_Lean_calcSteps___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_calcSteps___closed__8_value)}};
static const lean_object* l_Lean_calcSteps___closed__9 = (const lean_object*)&l_Lean_calcSteps___closed__9_value;
static const lean_ctor_object l_Lean_calcSteps___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__9_value)}};
static const lean_object* l_Lean_calcSteps___closed__10 = (const lean_object*)&l_Lean_calcSteps___closed__10_value;
static const lean_ctor_object l_Lean_calcSteps___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__10_value),((lean_object*)&l_Lean_calcStep___closed__5_value)}};
static const lean_object* l_Lean_calcSteps___closed__11 = (const lean_object*)&l_Lean_calcSteps___closed__11_value;
static const lean_ctor_object l_Lean_calcSteps___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_Lean_calcSteps___closed__11_value)}};
static const lean_object* l_Lean_calcSteps___closed__12 = (const lean_object*)&l_Lean_calcSteps___closed__12_value;
static const lean_ctor_object l_Lean_calcSteps___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_calcSteps___closed__12_value)}};
static const lean_object* l_Lean_calcSteps___closed__13 = (const lean_object*)&l_Lean_calcSteps___closed__13_value;
static const lean_ctor_object l_Lean_calcSteps___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcSteps___closed__6_value),((lean_object*)&l_Lean_calcSteps___closed__13_value)}};
static const lean_object* l_Lean_calcSteps___closed__14 = (const lean_object*)&l_Lean_calcSteps___closed__14_value;
static const lean_ctor_object l_Lean_calcSteps___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_calcSteps___closed__0_value),((lean_object*)&l_Lean_calcSteps___closed__1_value),((lean_object*)&l_Lean_calcSteps___closed__14_value)}};
static const lean_object* l_Lean_calcSteps___closed__15 = (const lean_object*)&l_Lean_calcSteps___closed__15_value;
LEAN_EXPORT const lean_object* l_Lean_calcSteps = (const lean_object*)&l_Lean_calcSteps___closed__15_value;
static const lean_string_object l_Lean_calc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "calc"};
static const lean_object* l_Lean_calc___closed__0 = (const lean_object*)&l_Lean_calc___closed__0_value;
static const lean_ctor_object l_Lean_calc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_calc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calc___closed__1_value_aux_0),((lean_object*)&l_Lean_calc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 46, 171, 201, 40, 237, 174, 33)}};
static const lean_object* l_Lean_calc___closed__1 = (const lean_object*)&l_Lean_calc___closed__1_value;
static const lean_ctor_object l_Lean_calc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_calc___closed__0_value)}};
static const lean_object* l_Lean_calc___closed__2 = (const lean_object*)&l_Lean_calc___closed__2_value;
static const lean_ctor_object l_Lean_calc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calc___closed__2_value),((lean_object*)&l_Lean_calcSteps___closed__15_value)}};
static const lean_object* l_Lean_calc___closed__3 = (const lean_object*)&l_Lean_calc___closed__3_value;
static const lean_ctor_object l_Lean_calc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_calc___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_calc___closed__3_value)}};
static const lean_object* l_Lean_calc___closed__4 = (const lean_object*)&l_Lean_calc___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_calc = (const lean_object*)&l_Lean_calc___closed__4_value;
static const lean_string_object l_Lean_calcTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "calcTactic"};
static const lean_object* l_Lean_calcTactic___closed__0 = (const lean_object*)&l_Lean_calcTactic___closed__0_value;
static const lean_ctor_object l_Lean_calcTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_calcTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_calcTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_calcTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 188, 49, 237, 47, 139, 25, 127)}};
static const lean_object* l_Lean_calcTactic___closed__1 = (const lean_object*)&l_Lean_calcTactic___closed__1_value;
static const lean_ctor_object l_Lean_calcTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_calc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_calcTactic___closed__2 = (const lean_object*)&l_Lean_calcTactic___closed__2_value;
static const lean_ctor_object l_Lean_calcTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcTactic___closed__2_value),((lean_object*)&l_Lean_calcSteps___closed__15_value)}};
static const lean_object* l_Lean_calcTactic___closed__3 = (const lean_object*)&l_Lean_calcTactic___closed__3_value;
static const lean_ctor_object l_Lean_calcTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_calcTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_calcTactic___closed__3_value)}};
static const lean_object* l_Lean_calcTactic___closed__4 = (const lean_object*)&l_Lean_calcTactic___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_calcTactic = (const lean_object*)&l_Lean_calcTactic___closed__4_value;
static const lean_string_object l_Lean_convCalc___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "convCalc_"};
static const lean_object* l_Lean_convCalc___00__closed__0 = (const lean_object*)&l_Lean_convCalc___00__closed__0_value;
static const lean_ctor_object l_Lean_convCalc___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_convCalc___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_convCalc___00__closed__1_value_aux_0),((lean_object*)&l_Lean_convCalc___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 82, 111, 111, 95, 3, 213, 249)}};
static const lean_object* l_Lean_convCalc___00__closed__1 = (const lean_object*)&l_Lean_convCalc___00__closed__1_value;
static const lean_ctor_object l_Lean_convCalc___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_convCalc___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_calcTactic___closed__3_value)}};
static const lean_object* l_Lean_convCalc___00__closed__2 = (const lean_object*)&l_Lean_convCalc___00__closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_convCalc__ = (const lean_object*)&l_Lean_convCalc___00__closed__2_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "nestedTactic"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value_aux_3),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 28, 213, 2, 207, 8, 223, 137)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__5 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__7 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandUnit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_fakeMod"};
static const lean_object* l_unexpandUnit___redArg___closed__0 = (const lean_object*)&l_unexpandUnit___redArg___closed__0_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandUnit___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 44, 241, 255, 153, 255, 67, 53)}};
static const lean_object* l_unexpandUnit___redArg___closed__1 = (const lean_object*)&l_unexpandUnit___redArg___closed__1_value;
static const lean_string_object l_unexpandUnit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l_unexpandUnit___redArg___closed__2 = (const lean_object*)&l_unexpandUnit___redArg___closed__2_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__3_value_aux_2),((lean_object*)&l_unexpandUnit___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l_unexpandUnit___redArg___closed__3 = (const lean_object*)&l_unexpandUnit___redArg___closed__3_value;
static const lean_string_object l_unexpandUnit___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_unexpandUnit___redArg___closed__4 = (const lean_object*)&l_unexpandUnit___redArg___closed__4_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_unexpandUnit___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__5_value_aux_2),((lean_object*)&l_unexpandUnit___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_unexpandUnit___redArg___closed__5 = (const lean_object*)&l_unexpandUnit___redArg___closed__5_value;
static const lean_string_object l_unexpandUnit___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_unexpandUnit___redArg___closed__6 = (const lean_object*)&l_unexpandUnit___redArg___closed__6_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandUnit___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_unexpandUnit___redArg___closed__7 = (const lean_object*)&l_unexpandUnit___redArg___closed__7_value;
static const lean_string_object l_unexpandUnit___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_unexpandUnit___redArg___closed__8 = (const lean_object*)&l_unexpandUnit___redArg___closed__8_value;
static lean_once_cell_t l_unexpandUnit___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_unexpandUnit___redArg___closed__9;
static lean_once_cell_t l_unexpandUnit___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_unexpandUnit___redArg___closed__10;
static const lean_ctor_object l_unexpandUnit___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_unexpandUnit___redArg___closed__11 = (const lean_object*)&l_unexpandUnit___redArg___closed__11_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_object* l_unexpandUnit___redArg___closed__12 = (const lean_object*)&l_unexpandUnit___redArg___closed__12_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__12_value)}};
static const lean_object* l_unexpandUnit___redArg___closed__13 = (const lean_object*)&l_unexpandUnit___redArg___closed__13_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_unexpandUnit___redArg___closed__14 = (const lean_object*)&l_unexpandUnit___redArg___closed__14_value;
static const lean_ctor_object l_unexpandUnit___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__11_value),((lean_object*)&l_unexpandUnit___redArg___closed__14_value)}};
static const lean_object* l_unexpandUnit___redArg___closed__15 = (const lean_object*)&l_unexpandUnit___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_unexpandUnit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandUnit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandUnit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandUnit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandListNil___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_unexpandListNil___redArg___closed__0 = (const lean_object*)&l_unexpandListNil___redArg___closed__0_value;
static const lean_ctor_object l_unexpandListNil___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandListNil___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_unexpandListNil___redArg___closed__1 = (const lean_object*)&l_unexpandListNil___redArg___closed__1_value;
static const lean_string_object l_unexpandListNil___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_unexpandListNil___redArg___closed__2 = (const lean_object*)&l_unexpandListNil___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_unexpandListNil___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandListNil___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandListNil(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandListNil___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandListCons___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "omission"};
static const lean_object* l_unexpandListCons___closed__0 = (const lean_object*)&l_unexpandListCons___closed__0_value;
static const lean_ctor_object l_unexpandListCons___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandListCons___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandListCons___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_unexpandListCons___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandListCons___closed__1_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_unexpandListCons___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandListCons___closed__1_value_aux_2),((lean_object*)&l_unexpandListCons___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 154, 52, 140, 5, 177, 16, 6)}};
static const lean_object* l_unexpandListCons___closed__1 = (const lean_object*)&l_unexpandListCons___closed__1_value;
LEAN_EXPORT lean_object* l_unexpandListCons(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandListCons___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandListToArray___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term#[_,]"};
static const lean_object* l_unexpandListToArray___closed__0 = (const lean_object*)&l_unexpandListToArray___closed__0_value;
static const lean_ctor_object l_unexpandListToArray___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandListToArray___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 119, 178, 128, 145, 112, 206, 247)}};
static const lean_object* l_unexpandListToArray___closed__1 = (const lean_object*)&l_unexpandListToArray___closed__1_value;
static const lean_string_object l_unexpandListToArray___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_unexpandListToArray___closed__2 = (const lean_object*)&l_unexpandListToArray___closed__2_value;
LEAN_EXPORT lean_object* l_unexpandListToArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandListToArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandProdMk(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandProdMk___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_unexpandIte___closed__0 = (const lean_object*)&l_unexpandIte___closed__0_value;
static const lean_ctor_object l_unexpandIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_unexpandIte___closed__1 = (const lean_object*)&l_unexpandIte___closed__1_value;
static const lean_string_object l_unexpandIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_unexpandIte___closed__2 = (const lean_object*)&l_unexpandIte___closed__2_value;
static const lean_string_object l_unexpandIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_unexpandIte___closed__3 = (const lean_object*)&l_unexpandIte___closed__3_value;
static const lean_string_object l_unexpandIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_unexpandIte___closed__4 = (const lean_object*)&l_unexpandIte___closed__4_value;
LEAN_EXPORT lean_object* l_unexpandIte(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandIte___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandEqNDRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_unexpandEqNDRec___closed__0 = (const lean_object*)&l_unexpandEqNDRec___closed__0_value;
static const lean_ctor_object l_unexpandEqNDRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandEqNDRec___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandEqNDRec___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_unexpandEqNDRec___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandEqNDRec___closed__1_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_unexpandEqNDRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandEqNDRec___closed__1_value_aux_2),((lean_object*)&l_unexpandEqNDRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 13, 108, 115, 152, 155, 29, 181)}};
static const lean_object* l_unexpandEqNDRec___closed__1 = (const lean_object*)&l_unexpandEqNDRec___closed__1_value;
static const lean_string_object l_unexpandEqNDRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "▸"};
static const lean_object* l_unexpandEqNDRec___closed__2 = (const lean_object*)&l_unexpandEqNDRec___closed__2_value;
LEAN_EXPORT lean_object* l_unexpandEqNDRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandEqNDRec___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandEqRec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandEqRec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l_unexpandExists___closed__0 = (const lean_object*)&l_unexpandExists___closed__0_value;
static const lean_ctor_object l_unexpandExists___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandExists___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandExists___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_unexpandExists___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandExists___closed__1_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_unexpandExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandExists___closed__1_value_aux_2),((lean_object*)&l_unexpandExists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l_unexpandExists___closed__1 = (const lean_object*)&l_unexpandExists___closed__1_value;
static const lean_string_object l_unexpandExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_unexpandExists___closed__2 = (const lean_object*)&l_unexpandExists___closed__2_value;
static const lean_ctor_object l_unexpandExists___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_unexpandExists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandExists___closed__3_value_aux_0),((lean_object*)&l_unexpandExists___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_unexpandExists___closed__3 = (const lean_object*)&l_unexpandExists___closed__3_value;
LEAN_EXPORT lean_object* l_unexpandExists(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "×"};
static const lean_object* l_unexpandSigma___closed__0 = (const lean_object*)&l_unexpandSigma___closed__0_value;
LEAN_EXPORT lean_object* l_unexpandSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandSigma___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandPSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "×'"};
static const lean_object* l_unexpandPSigma___closed__0 = (const lean_object*)&l_unexpandPSigma___closed__0_value;
LEAN_EXPORT lean_object* l_unexpandPSigma(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandPSigma___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandSubtype___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "term{_:_//_}"};
static const lean_object* l_unexpandSubtype___closed__0 = (const lean_object*)&l_unexpandSubtype___closed__0_value;
static const lean_ctor_object l_unexpandSubtype___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandSubtype___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 133, 82, 74, 101, 189, 164, 87)}};
static const lean_object* l_unexpandSubtype___closed__1 = (const lean_object*)&l_unexpandSubtype___closed__1_value;
static const lean_string_object l_unexpandSubtype___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_unexpandSubtype___closed__2 = (const lean_object*)&l_unexpandSubtype___closed__2_value;
static const lean_string_object l_unexpandSubtype___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "//"};
static const lean_object* l_unexpandSubtype___closed__3 = (const lean_object*)&l_unexpandSubtype___closed__3_value;
static const lean_string_object l_unexpandSubtype___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_unexpandSubtype___closed__4 = (const lean_object*)&l_unexpandSubtype___closed__4_value;
LEAN_EXPORT lean_object* l_unexpandSubtype(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandSubtype___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSyntax(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSyntax___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSepArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandTSepArray___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandGetElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term__[_]"};
static const lean_object* l_unexpandGetElem___closed__0 = (const lean_object*)&l_unexpandGetElem___closed__0_value;
static const lean_ctor_object l_unexpandGetElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandGetElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 68, 146, 84, 128, 183, 70, 246)}};
static const lean_object* l_unexpandGetElem___closed__1 = (const lean_object*)&l_unexpandGetElem___closed__1_value;
LEAN_EXPORT lean_object* l_unexpandGetElem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandGetElem___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandGetElem_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_!"};
static const lean_object* l_unexpandGetElem_x21___closed__0 = (const lean_object*)&l_unexpandGetElem_x21___closed__0_value;
static const lean_ctor_object l_unexpandGetElem_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandGetElem_x21___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 145, 92, 47, 59, 8, 18, 13)}};
static const lean_object* l_unexpandGetElem_x21___closed__1 = (const lean_object*)&l_unexpandGetElem_x21___closed__1_value;
static const lean_string_object l_unexpandGetElem_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l_unexpandGetElem_x21___closed__2 = (const lean_object*)&l_unexpandGetElem_x21___closed__2_value;
LEAN_EXPORT lean_object* l_unexpandGetElem_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandGetElem_x21___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_unexpandGetElem_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "term__[_]_\?"};
static const lean_object* l_unexpandGetElem_x3f___closed__0 = (const lean_object*)&l_unexpandGetElem_x3f___closed__0_value;
static const lean_ctor_object l_unexpandGetElem_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_unexpandGetElem_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 178, 109, 68, 161, 229, 23, 17)}};
static const lean_object* l_unexpandGetElem_x3f___closed__1 = (const lean_object*)&l_unexpandGetElem_x3f___closed__1_value;
static const lean_string_object l_unexpandGetElem_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_unexpandGetElem_x3f___closed__2 = (const lean_object*)&l_unexpandGetElem_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandArrayEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_unexpandMkArray8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_tacticFunext_______00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "tacticFunext___"};
static const lean_object* l_tacticFunext_______00__closed__0 = (const lean_object*)&l_tacticFunext_______00__closed__0_value;
static const lean_ctor_object l_tacticFunext_______00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticFunext_______00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 155, 131, 24, 73, 26, 166, 240)}};
static const lean_object* l_tacticFunext_______00__closed__1 = (const lean_object*)&l_tacticFunext_______00__closed__1_value;
static const lean_string_object l_tacticFunext_______00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "funext"};
static const lean_object* l_tacticFunext_______00__closed__2 = (const lean_object*)&l_tacticFunext_______00__closed__2_value;
static const lean_ctor_object l_tacticFunext_______00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_tacticFunext_______00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_tacticFunext_______00__closed__3 = (const lean_object*)&l_tacticFunext_______00__closed__3_value;
static const lean_string_object l_tacticFunext_______00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "colGt"};
static const lean_object* l_tacticFunext_______00__closed__4 = (const lean_object*)&l_tacticFunext_______00__closed__4_value;
static const lean_ctor_object l_tacticFunext_______00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticFunext_______00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(185, 236, 32, 153, 169, 213, 53, 244)}};
static const lean_object* l_tacticFunext_______00__closed__5 = (const lean_object*)&l_tacticFunext_______00__closed__5_value;
static const lean_ctor_object l_tacticFunext_______00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_tacticFunext_______00__closed__5_value)}};
static const lean_object* l_tacticFunext_______00__closed__6 = (const lean_object*)&l_tacticFunext_______00__closed__6_value;
static const lean_ctor_object l_tacticFunext_______00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__9_value),((lean_object*)&l_tacticFunext_______00__closed__6_value)}};
static const lean_object* l_tacticFunext_______00__closed__7 = (const lean_object*)&l_tacticFunext_______00__closed__7_value;
static const lean_ctor_object l_tacticFunext_______00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__17_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_tacticFunext_______00__closed__8 = (const lean_object*)&l_tacticFunext_______00__closed__8_value;
static const lean_ctor_object l_tacticFunext_______00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_tacticFunext_______00__closed__7_value),((lean_object*)&l_tacticFunext_______00__closed__8_value)}};
static const lean_object* l_tacticFunext_______00__closed__9 = (const lean_object*)&l_tacticFunext_______00__closed__9_value;
static const lean_ctor_object l_tacticFunext_______00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_tacticFunext_______00__closed__9_value)}};
static const lean_object* l_tacticFunext_______00__closed__10 = (const lean_object*)&l_tacticFunext_______00__closed__10_value;
static const lean_ctor_object l_tacticFunext_______00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_tacticFunext_______00__closed__3_value),((lean_object*)&l_tacticFunext_______00__closed__10_value)}};
static const lean_object* l_tacticFunext_______00__closed__11 = (const lean_object*)&l_tacticFunext_______00__closed__11_value;
static const lean_ctor_object l_tacticFunext_______00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_tacticFunext_______00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_tacticFunext_______00__closed__11_value)}};
static const lean_object* l_tacticFunext_______00__closed__12 = (const lean_object*)&l_tacticFunext_______00__closed__12_value;
LEAN_EXPORT const lean_object* l_tacticFunext______ = (const lean_object*)&l_tacticFunext_______00__closed__12_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "seq1"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 140, 137, 56, 141, 11, 143, 117)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3_value;
static lean_once_cell_t l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_tacticFunext_______00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(226, 251, 226, 140, 5, 134, 146, 130)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__6 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__6_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 145, 9, 18, 75, 146, 159, 78)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "tacticRepeat_"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__11 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__11_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(149, 101, 42, 245, 144, 172, 68, 230)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__14 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__14_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "List.cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__5_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__7_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term%[_|_]"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 149, 151, 28, 109, 173, 225, 162)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "let"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 166, 195, 152, 24, 103, 8, 2)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letConfig"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__4 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__4_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(5, 186, 227, 151, 19, 40, 136, 241)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__6 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__6_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__8 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__8_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "letId"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__10 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__10_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(67, 92, 92, 51, 38, 250, 60, 190)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12_value;
static lean_once_cell_t l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "%["};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15_value;
static lean_once_cell_t l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Command_classAbbrev___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "classAbbrev"};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__0 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__0_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__1_value_aux_2),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 112, 139, 141, 120, 66, 29, 3)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__1 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__1_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(113, 135, 0, 93, 130, 217, 220, 132)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__2 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__2_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__2_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__3 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__3_value;
static const lean_string_object l_Lean_Parser_Command_classAbbrev___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "class "};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__4 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__4_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__4_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__5 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__5_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__3_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__5_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__6 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__6_value;
static const lean_string_object l_Lean_Parser_Command_classAbbrev___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "abbrev "};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__7 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__7_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__7_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__8 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__8_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__6_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__8_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__9 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__9_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(210, 155, 24, 168, 139, 44, 164, 47)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__10 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__10_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__10_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__11 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__11_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__9_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__11_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__12 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__12_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__23_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__13 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__13_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__12_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__13_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__14 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__14_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__15 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__15_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__15_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__16 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__16_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__16_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__17 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__17_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__14_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__18 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__18_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__19 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__19_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__18_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__19_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__20 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__20_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__21 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__21_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__13_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__21_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__22 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__22_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_calcFirstStep___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__22_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__23 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__23_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__23_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__24 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__24_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__20_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__24_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__25 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__25_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__25_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__26 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__26_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__20_value),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__26_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__27 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__27_value;
static const lean_ctor_object l_Lean_Parser_Command_classAbbrev___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__27_value)}};
static const lean_object* l_Lean_Parser_Command_classAbbrev___closed__28 = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__28_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Command_classAbbrev = (const lean_object*)&l_Lean_Parser_Command_classAbbrev___closed__28_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__0_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 247, 82, 130, 198, 123, 173)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "structParent"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 41, 245, 205, 163, 229, 236, 195)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extends"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 24, 97, 144, 91, 250, 92, 29)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "optDeriving"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__3 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__3_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(215, 163, 253, 206, 79, 89, 101, 240)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(128, 1, 138, 227, 223, 112, 103, 179)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__10 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__10_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "classTk"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__12 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__12_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(166, 117, 114, 200, 210, 60, 33, 9)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "class"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_cdotTk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_Lean_cdotTk___closed__0 = (const lean_object*)&l_Lean_cdotTk___closed__0_value;
static const lean_ctor_object l_Lean_cdotTk___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_cdotTk___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_cdotTk___closed__1_value_aux_0),((lean_object*)&l_Lean_cdotTk___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_Lean_cdotTk___closed__1 = (const lean_object*)&l_Lean_cdotTk___closed__1_value;
static const lean_string_object l_Lean_cdotTk___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "· "};
static const lean_object* l_Lean_cdotTk___closed__2 = (const lean_object*)&l_Lean_cdotTk___closed__2_value;
static const lean_string_object l_Lean_cdotTk___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ". "};
static const lean_object* l_Lean_cdotTk___closed__3 = (const lean_object*)&l_Lean_cdotTk___closed__3_value;
static const lean_ctor_object l_Lean_cdotTk___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean_cdotTk___closed__2_value),((lean_object*)&l_Lean_cdotTk___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_cdotTk___closed__4 = (const lean_object*)&l_Lean_cdotTk___closed__4_value;
static const lean_ctor_object l_Lean_cdotTk___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 9}, .m_objs = {((lean_object*)&l_Lean_cdotTk___closed__0_value),((lean_object*)&l_Lean_cdotTk___closed__1_value),((lean_object*)&l_Lean_cdotTk___closed__4_value)}};
static const lean_object* l_Lean_cdotTk___closed__5 = (const lean_object*)&l_Lean_cdotTk___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_cdotTk = (const lean_object*)&l_Lean_cdotTk___closed__5_value;
static const lean_string_object l_Lean_cdot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Lean_cdot___closed__0 = (const lean_object*)&l_Lean_cdot___closed__0_value;
static const lean_ctor_object l_Lean_cdot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_cdot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_cdot___closed__1_value_aux_0),((lean_object*)&l_Lean_cdot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 151, 138, 49, 249, 18, 254, 242)}};
static const lean_object* l_Lean_cdot___closed__1 = (const lean_object*)&l_Lean_cdot___closed__1_value;
static const lean_string_object l_Lean_cdot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tacticSeqIndentGt"};
static const lean_object* l_Lean_cdot___closed__2 = (const lean_object*)&l_Lean_cdot___closed__2_value;
static const lean_ctor_object l_Lean_cdot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_cdot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(13, 96, 154, 40, 0, 37, 199, 17)}};
static const lean_object* l_Lean_cdot___closed__3 = (const lean_object*)&l_Lean_cdot___closed__3_value;
static const lean_ctor_object l_Lean_cdot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_cdot___closed__3_value)}};
static const lean_object* l_Lean_cdot___closed__4 = (const lean_object*)&l_Lean_cdot___closed__4_value;
static const lean_ctor_object l_Lean_cdot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_cdotTk___closed__5_value),((lean_object*)&l_Lean_cdot___closed__4_value)}};
static const lean_object* l_Lean_cdot___closed__5 = (const lean_object*)&l_Lean_cdot___closed__5_value;
static const lean_ctor_object l_Lean_cdot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_cdot___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_cdot___closed__5_value)}};
static const lean_object* l_Lean_cdot___closed__6 = (const lean_object*)&l_Lean_cdot___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_cdot = (const lean_object*)&l_Lean_cdot___closed__6_value;
static const lean_string_object l_Lean_solveTactic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "solveTactic"};
static const lean_object* l_Lean_solveTactic___closed__0 = (const lean_object*)&l_Lean_solveTactic___closed__0_value;
static const lean_ctor_object l_Lean_solveTactic___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_solveTactic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__1_value_aux_0),((lean_object*)&l_Lean_solveTactic___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 93, 240, 221, 8, 79, 216, 244)}};
static const lean_object* l_Lean_solveTactic___closed__1 = (const lean_object*)&l_Lean_solveTactic___closed__1_value;
static const lean_string_object l_Lean_solveTactic___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "solve"};
static const lean_object* l_Lean_solveTactic___closed__2 = (const lean_object*)&l_Lean_solveTactic___closed__2_value;
static const lean_ctor_object l_Lean_solveTactic___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_solveTactic___closed__3 = (const lean_object*)&l_Lean_solveTactic___closed__3_value;
static const lean_string_object l_Lean_solveTactic___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_solveTactic___closed__4 = (const lean_object*)&l_Lean_solveTactic___closed__4_value;
static const lean_ctor_object l_Lean_solveTactic___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_solveTactic___closed__4_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_solveTactic___closed__5 = (const lean_object*)&l_Lean_solveTactic___closed__5_value;
static const lean_ctor_object l_Lean_solveTactic___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__5_value),((lean_object*)&l_Lean_calcSteps___closed__4_value)}};
static const lean_object* l_Lean_solveTactic___closed__6 = (const lean_object*)&l_Lean_solveTactic___closed__6_value;
static const lean_ctor_object l_Lean_solveTactic___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_solveTactic___closed__6_value),((lean_object*)&l_Lean_unifConstraintElem___closed__4_value)}};
static const lean_object* l_Lean_solveTactic___closed__7 = (const lean_object*)&l_Lean_solveTactic___closed__7_value;
static const lean_string_object l_Lean_solveTactic___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "| "};
static const lean_object* l_Lean_solveTactic___closed__8 = (const lean_object*)&l_Lean_solveTactic___closed__8_value;
static const lean_ctor_object l_Lean_solveTactic___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__8_value)}};
static const lean_object* l_Lean_solveTactic___closed__9 = (const lean_object*)&l_Lean_solveTactic___closed__9_value;
static const lean_ctor_object l_Lean_solveTactic___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_solveTactic___closed__7_value),((lean_object*)&l_Lean_solveTactic___closed__9_value)}};
static const lean_object* l_Lean_solveTactic___closed__10 = (const lean_object*)&l_Lean_solveTactic___closed__10_value;
static const lean_ctor_object l_Lean_solveTactic___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 106, 54, 236, 164, 218, 24, 154)}};
static const lean_object* l_Lean_solveTactic___closed__11 = (const lean_object*)&l_Lean_solveTactic___closed__11_value;
static const lean_ctor_object l_Lean_solveTactic___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__11_value)}};
static const lean_object* l_Lean_solveTactic___closed__12 = (const lean_object*)&l_Lean_solveTactic___closed__12_value;
static const lean_ctor_object l_Lean_solveTactic___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_solveTactic___closed__10_value),((lean_object*)&l_Lean_solveTactic___closed__12_value)}};
static const lean_object* l_Lean_solveTactic___closed__13 = (const lean_object*)&l_Lean_solveTactic___closed__13_value;
static const lean_ctor_object l_Lean_solveTactic___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38_value),((lean_object*)&l_Lean_solveTactic___closed__13_value)}};
static const lean_object* l_Lean_solveTactic___closed__14 = (const lean_object*)&l_Lean_solveTactic___closed__14_value;
static const lean_ctor_object l_Lean_solveTactic___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__6_value),((lean_object*)&l_Lean_solveTactic___closed__14_value)}};
static const lean_object* l_Lean_solveTactic___closed__15 = (const lean_object*)&l_Lean_solveTactic___closed__15_value;
static const lean_ctor_object l_Lean_solveTactic___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_solveTactic___closed__15_value)}};
static const lean_object* l_Lean_solveTactic___closed__16 = (const lean_object*)&l_Lean_solveTactic___closed__16_value;
static const lean_ctor_object l_Lean_solveTactic___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_solveTactic___closed__3_value),((lean_object*)&l_Lean_solveTactic___closed__16_value)}};
static const lean_object* l_Lean_solveTactic___closed__17 = (const lean_object*)&l_Lean_solveTactic___closed__17_value;
static const lean_ctor_object l_Lean_solveTactic___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_solveTactic___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_solveTactic___closed__17_value)}};
static const lean_object* l_Lean_solveTactic___closed__18 = (const lean_object*)&l_Lean_solveTactic___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_solveTactic = (const lean_object*)&l_Lean_solveTactic___closed__18_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "focus"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 223, 207, 6, 131, 57, 182, 221)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_term__Matches___x7c___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "term_Matches_|"};
static const lean_object* l_Lean_term__Matches___x7c___closed__0 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__0_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_term__Matches___x7c___closed__1_value_aux_0),((lean_object*)&l_Lean_term__Matches___x7c___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 90, 108, 139, 70, 136, 238, 145)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__1 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__1_value;
static const lean_string_object l_Lean_term__Matches___x7c___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " matches "};
static const lean_object* l_Lean_term__Matches___x7c___closed__2 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__2_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_term__Matches___x7c___closed__2_value)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__3 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__3_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__17_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Lean_term__Matches___x7c___closed__4 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__4_value;
static const lean_string_object l_Lean_term__Matches___x7c___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " | "};
static const lean_object* l_Lean_term__Matches___x7c___closed__5 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__5_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_term__Matches___x7c___closed__5_value)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__6 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__6_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_term__Matches___x7c___closed__4_value),((lean_object*)&l_Lean_term__Matches___x7c___closed__5_value),((lean_object*)&l_Lean_term__Matches___x7c___closed__6_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__7 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__7_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_Lean_term__Matches___x7c___closed__3_value),((lean_object*)&l_Lean_term__Matches___x7c___closed__7_value)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__8 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__8_value;
static const lean_ctor_object l_Lean_term__Matches___x7c___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Lean_term__Matches___x7c___closed__1_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Lean_term__Matches___x7c___closed__8_value)}};
static const lean_object* l_Lean_term__Matches___x7c___closed__9 = (const lean_object*)&l_Lean_term__Matches___x7c___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_term__Matches___x7c = (const lean_object*)&l_Lean_term__Matches___x7c___closed__9_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_unexpandUnit___redArg___closed__13_value),((lean_object*)&l_unexpandUnit___redArg___closed__14_value)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value_aux_2),((lean_object*)&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__4 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__4_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__7 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__9 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__9_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_0),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_1),((lean_object*)&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value_aux_2),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(235, 97, 249, 134, 197, 220, 12, 91)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16_value_aux_0),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__17 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__17_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18_value;
static const lean_string_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(160, 214, 196, 140, 104, 187, 164, 111)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22_value_aux_0),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__23 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__23_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24_value;
static lean_once_cell_t l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__27 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__27_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26_value)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__28 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__28_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__28_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__29 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__29_value;
static const lean_ctor_object l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__27_value),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__29_value)}};
static const lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30 = (const lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term_x7b___x7d___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term{_}"};
static const lean_object* l_term_x7b___x7d___closed__0 = (const lean_object*)&l_term_x7b___x7d___closed__0_value;
static const lean_ctor_object l_term_x7b___x7d___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term_x7b___x7d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 26, 220, 95, 138, 254, 219, 101)}};
static const lean_object* l_term_x7b___x7d___closed__1 = (const lean_object*)&l_term_x7b___x7d___closed__1_value;
static const lean_ctor_object l_term_x7b___x7d___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_unexpandSubtype___closed__2_value)}};
static const lean_object* l_term_x7b___x7d___closed__2 = (const lean_object*)&l_term_x7b___x7d___closed__2_value;
static const lean_ctor_object l_term_x7b___x7d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17_value),((lean_object*)&l_Lean_unifConstraintElem___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_term_x7b___x7d___closed__3 = (const lean_object*)&l_term_x7b___x7d___closed__3_value;
static const lean_ctor_object l_term_x7b___x7d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_term_x7b___x7d___closed__2_value),((lean_object*)&l_term_x7b___x7d___closed__3_value)}};
static const lean_object* l_term_x7b___x7d___closed__4 = (const lean_object*)&l_term_x7b___x7d___closed__4_value;
static const lean_ctor_object l_term_x7b___x7d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_unexpandSubtype___closed__4_value)}};
static const lean_object* l_term_x7b___x7d___closed__5 = (const lean_object*)&l_term_x7b___x7d___closed__5_value;
static const lean_ctor_object l_term_x7b___x7d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_term_x7b___x7d___closed__4_value),((lean_object*)&l_term_x7b___x7d___closed__5_value)}};
static const lean_object* l_term_x7b___x7d___closed__6 = (const lean_object*)&l_term_x7b___x7d___closed__6_value;
static const lean_ctor_object l_term_x7b___x7d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x7b___x7d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x7b___x7d___closed__6_value)}};
static const lean_object* l_term_x7b___x7d___closed__7 = (const lean_object*)&l_term_x7b___x7d___closed__7_value;
LEAN_EXPORT const lean_object* l_term_x7b___x7d = (const lean_object*)&l_term_x7b___x7d___closed__7_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "insert"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0_value;
static lean_once_cell_t l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 186, 105, 165, 216, 51, 157, 222)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Insert"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__3 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__3_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(126, 209, 156, 174, 188, 62, 109, 85)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 132, 219, 243, 180, 219, 203, 85)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__5 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__5_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "singleton"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7_value;
static lean_once_cell_t l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 33, 246, 107, 223, 5, 156, 82)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9_value;
static const lean_string_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Singleton"};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__10 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__10_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(190, 73, 36, 155, 228, 35, 161, 122)}};
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11_value_aux_0),((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(185, 48, 115, 60, 21, 14, 217, 215)}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__12 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__12_value;
static const lean_ctor_object l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13 = (const lean_object*)&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13_value;
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_insertUnexpander(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_insertUnexpander___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_unbracketedExplicitBinders___closed__10(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = l_Lean_binderIdent;
v___x_18_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__9));
v___x_19_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_20_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_unbracketedExplicitBinders___closed__11(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Lean_unbracketedExplicitBinders___closed__10, &l_Lean_unbracketedExplicitBinders___closed__10_once, _init_l_Lean_unbracketedExplicitBinders___closed__10);
v___x_22_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__6));
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___x_21_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_unbracketedExplicitBinders___closed__21(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_43_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__20));
v___x_44_ = lean_obj_once(&l_Lean_unbracketedExplicitBinders___closed__11, &l_Lean_unbracketedExplicitBinders___closed__11_once, _init_l_Lean_unbracketedExplicitBinders___closed__11);
v___x_45_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_46_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v___x_44_);
lean_ctor_set(v___x_46_, 2, v___x_43_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_unbracketedExplicitBinders___closed__22(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Lean_unbracketedExplicitBinders___closed__21, &l_Lean_unbracketedExplicitBinders___closed__21_once, _init_l_Lean_unbracketedExplicitBinders___closed__21);
v___x_48_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_49_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__0));
v___x_50_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_unbracketedExplicitBinders(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Lean_unbracketedExplicitBinders___closed__22, &l_Lean_unbracketedExplicitBinders___closed__22_once, _init_l_Lean_unbracketedExplicitBinders___closed__22);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__6(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__9));
v___x_63_ = l_Lean_binderIdent;
v___x_64_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_65_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__7(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__6, &l_Lean_bracketedExplicitBinders___closed__6_once, _init_l_Lean_bracketedExplicitBinders___closed__6);
v___x_67_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__6));
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_66_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__10(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__9));
v___x_73_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__7, &l_Lean_bracketedExplicitBinders___closed__7_once, _init_l_Lean_bracketedExplicitBinders___closed__7);
v___x_74_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_75_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_72_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__11(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_77_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__10, &l_Lean_bracketedExplicitBinders___closed__10_once, _init_l_Lean_bracketedExplicitBinders___closed__10);
v___x_78_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_79_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_76_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__12(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__11, &l_Lean_bracketedExplicitBinders___closed__11_once, _init_l_Lean_bracketedExplicitBinders___closed__11);
v___x_81_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__5));
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__13(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__12, &l_Lean_bracketedExplicitBinders___closed__12_once, _init_l_Lean_bracketedExplicitBinders___closed__12);
v___x_84_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__3));
v___x_85_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_86_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__16(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__15));
v___x_91_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__13, &l_Lean_bracketedExplicitBinders___closed__13_once, _init_l_Lean_bracketedExplicitBinders___closed__13);
v___x_92_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_93_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders___closed__17(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__16, &l_Lean_bracketedExplicitBinders___closed__16_once, _init_l_Lean_bracketedExplicitBinders___closed__16);
v___x_95_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_96_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__0));
v___x_97_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_bracketedExplicitBinders(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_bracketedExplicitBinders___closed__17, &l_Lean_bracketedExplicitBinders___closed__17_once, _init_l_Lean_bracketedExplicitBinders___closed__17);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_explicitBinders___closed__4(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_106_ = l_Lean_bracketedExplicitBinders;
v___x_107_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__9));
v___x_108_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_109_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___x_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_explicitBinders___closed__5(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_obj_once(&l_Lean_explicitBinders___closed__4, &l_Lean_explicitBinders___closed__4_once, _init_l_Lean_explicitBinders___closed__4);
v___x_111_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__6));
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_explicitBinders___closed__6(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = l_Lean_unbracketedExplicitBinders;
v___x_114_ = lean_obj_once(&l_Lean_explicitBinders___closed__5, &l_Lean_explicitBinders___closed__5_once, _init_l_Lean_explicitBinders___closed__5);
v___x_115_ = ((lean_object*)(l_Lean_explicitBinders___closed__3));
v___x_116_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
return v___x_116_;
}
}
static lean_object* _init_l_Lean_explicitBinders___closed__7(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = lean_obj_once(&l_Lean_explicitBinders___closed__6, &l_Lean_explicitBinders___closed__6_once, _init_l_Lean_explicitBinders___closed__6);
v___x_118_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_119_ = ((lean_object*)(l_Lean_explicitBinders___closed__0));
v___x_120_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_explicitBinders(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&l_Lean_explicitBinders___closed__7, &l_Lean_explicitBinders___closed__7_once, _init_l_Lean_explicitBinders___closed__7);
return v___x_121_;
}
}
static lean_object* _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13(void){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Array_mkArray0(lean_box(0));
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg(lean_object* v_combinator_161_, lean_object* v_idents_162_, lean_object* v_type_x3f_163_, lean_object* v_i_164_, lean_object* v_acc_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_zero_168_; uint8_t v_isZero_169_; 
v_zero_168_ = lean_unsigned_to_nat(0u);
v_isZero_169_ = lean_nat_dec_eq(v_i_164_, v_zero_168_);
if (v_isZero_169_ == 1)
{
lean_object* v___x_170_; 
lean_dec(v_i_164_);
lean_dec(v_type_x3f_163_);
lean_dec(v_combinator_161_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v_acc_165_);
lean_ctor_set(v___x_170_, 1, v_a_167_);
return v___x_170_;
}
else
{
lean_object* v_one_171_; lean_object* v_n_172_; lean_object* v___x_173_; lean_object* v_ident_174_; uint8_t v___x_175_; 
v_one_171_ = lean_unsigned_to_nat(1u);
v_n_172_ = lean_nat_sub(v_i_164_, v_one_171_);
lean_dec(v_i_164_);
v___x_173_ = lean_array_fget_borrowed(v_idents_162_, v_n_172_);
v_ident_174_ = l_Lean_Syntax_getArg(v___x_173_, v_zero_168_);
v___x_175_ = l_Lean_Syntax_isIdent(v_ident_174_);
if (v___x_175_ == 0)
{
lean_dec(v_ident_174_);
if (lean_obj_tag(v_type_x3f_163_) == 0)
{
lean_object* v_ref_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_ref_176_ = lean_ctor_get(v_a_166_, 5);
v___x_177_ = l_Lean_SourceInfo_fromRef(v_ref_176_, v___x_175_);
v___x_178_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_179_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_180_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6));
v___x_181_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc_n(v___x_177_, 9);
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_177_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
v___x_183_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
v___x_184_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11));
v___x_185_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_186_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_177_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = l_Lean_Syntax_node1(v___x_177_, v___x_184_, v___x_186_);
v___x_188_ = l_Lean_Syntax_node1(v___x_177_, v___x_179_, v___x_187_);
v___x_189_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_190_, 0, v___x_177_);
lean_ctor_set(v___x_190_, 1, v___x_179_);
lean_ctor_set(v___x_190_, 2, v___x_189_);
v___x_191_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_192_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_177_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_Syntax_node4(v___x_177_, v___x_183_, v___x_188_, v___x_190_, v___x_192_, v_acc_165_);
v___x_194_ = l_Lean_Syntax_node2(v___x_177_, v___x_181_, v___x_182_, v___x_193_);
v___x_195_ = l_Lean_Syntax_node1(v___x_177_, v___x_179_, v___x_194_);
lean_inc(v_combinator_161_);
v___x_196_ = l_Lean_Syntax_node2(v___x_177_, v___x_178_, v_combinator_161_, v___x_195_);
v_i_164_ = v_n_172_;
v_acc_165_ = v___x_196_;
goto _start;
}
else
{
lean_object* v_val_198_; lean_object* v_ref_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_val_198_ = lean_ctor_get(v_type_x3f_163_, 0);
v_ref_199_ = lean_ctor_get(v_a_166_, 5);
v___x_200_ = l_Lean_SourceInfo_fromRef(v_ref_199_, v___x_175_);
v___x_201_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_202_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_203_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6));
v___x_204_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc_n(v___x_200_, 11);
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_200_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
v___x_206_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
v___x_207_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11));
v___x_208_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_200_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = l_Lean_Syntax_node1(v___x_200_, v___x_207_, v___x_209_);
v___x_211_ = l_Lean_Syntax_node1(v___x_200_, v___x_202_, v___x_210_);
v___x_212_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16));
v___x_213_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_214_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_200_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
lean_inc(v_val_198_);
v___x_215_ = l_Lean_Syntax_node2(v___x_200_, v___x_212_, v___x_214_, v_val_198_);
v___x_216_ = l_Lean_Syntax_node1(v___x_200_, v___x_202_, v___x_215_);
v___x_217_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_200_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = l_Lean_Syntax_node4(v___x_200_, v___x_206_, v___x_211_, v___x_216_, v___x_218_, v_acc_165_);
v___x_220_ = l_Lean_Syntax_node2(v___x_200_, v___x_204_, v___x_205_, v___x_219_);
v___x_221_ = l_Lean_Syntax_node1(v___x_200_, v___x_202_, v___x_220_);
lean_inc(v_combinator_161_);
v___x_222_ = l_Lean_Syntax_node2(v___x_200_, v___x_201_, v_combinator_161_, v___x_221_);
v_i_164_ = v_n_172_;
v_acc_165_ = v___x_222_;
goto _start;
}
}
else
{
if (lean_obj_tag(v_type_x3f_163_) == 0)
{
lean_object* v_ref_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v_ref_224_ = lean_ctor_get(v_a_166_, 5);
v___x_225_ = l_Lean_SourceInfo_fromRef(v_ref_224_, v_isZero_169_);
v___x_226_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_227_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_228_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6));
v___x_229_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc_n(v___x_225_, 7);
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
lean_ctor_set(v___x_230_, 1, v___x_228_);
v___x_231_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
v___x_232_ = l_Lean_Syntax_node1(v___x_225_, v___x_227_, v_ident_174_);
v___x_233_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_234_, 0, v___x_225_);
lean_ctor_set(v___x_234_, 1, v___x_227_);
lean_ctor_set(v___x_234_, 2, v___x_233_);
v___x_235_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_236_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_225_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = l_Lean_Syntax_node4(v___x_225_, v___x_231_, v___x_232_, v___x_234_, v___x_236_, v_acc_165_);
v___x_238_ = l_Lean_Syntax_node2(v___x_225_, v___x_229_, v___x_230_, v___x_237_);
v___x_239_ = l_Lean_Syntax_node1(v___x_225_, v___x_227_, v___x_238_);
lean_inc(v_combinator_161_);
v___x_240_ = l_Lean_Syntax_node2(v___x_225_, v___x_226_, v_combinator_161_, v___x_239_);
v_i_164_ = v_n_172_;
v_acc_165_ = v___x_240_;
goto _start;
}
else
{
lean_object* v_val_242_; lean_object* v_ref_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_val_242_ = lean_ctor_get(v_type_x3f_163_, 0);
v_ref_243_ = lean_ctor_get(v_a_166_, 5);
v___x_244_ = l_Lean_SourceInfo_fromRef(v_ref_243_, v_isZero_169_);
v___x_245_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_246_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_247_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__6));
v___x_248_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc_n(v___x_244_, 9);
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_244_);
lean_ctor_set(v___x_249_, 1, v___x_247_);
v___x_250_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
v___x_251_ = l_Lean_Syntax_node1(v___x_244_, v___x_246_, v_ident_174_);
v___x_252_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__16));
v___x_253_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_244_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
lean_inc(v_val_242_);
v___x_255_ = l_Lean_Syntax_node2(v___x_244_, v___x_252_, v___x_254_, v_val_242_);
v___x_256_ = l_Lean_Syntax_node1(v___x_244_, v___x_246_, v___x_255_);
v___x_257_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_258_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_244_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Lean_Syntax_node4(v___x_244_, v___x_250_, v___x_251_, v___x_256_, v___x_258_, v_acc_165_);
v___x_260_ = l_Lean_Syntax_node2(v___x_244_, v___x_248_, v___x_249_, v___x_259_);
v___x_261_ = l_Lean_Syntax_node1(v___x_244_, v___x_246_, v___x_260_);
lean_inc(v_combinator_161_);
v___x_262_ = l_Lean_Syntax_node2(v___x_244_, v___x_245_, v_combinator_161_, v___x_261_);
v_i_164_ = v_n_172_;
v_acc_165_ = v___x_262_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___boxed(lean_object* v_combinator_264_, lean_object* v_idents_265_, lean_object* v_type_x3f_266_, lean_object* v_i_267_, lean_object* v_acc_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg(v_combinator_264_, v_idents_265_, v_type_x3f_266_, v_i_267_, v_acc_268_, v_a_269_, v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_idents_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop(lean_object* v_combinator_272_, lean_object* v_idents_273_, lean_object* v_type_x3f_274_, lean_object* v_i_275_, lean_object* v_h_276_, lean_object* v_acc_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg(v_combinator_272_, v_idents_273_, v_type_x3f_274_, v_i_275_, v_acc_277_, v_a_278_, v_a_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___boxed(lean_object* v_combinator_281_, lean_object* v_idents_282_, lean_object* v_type_x3f_283_, lean_object* v_i_284_, lean_object* v_h_285_, lean_object* v_acc_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop(v_combinator_281_, v_idents_282_, v_type_x3f_283_, v_i_284_, v_h_285_, v_acc_286_, v_a_287_, v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec_ref(v_idents_282_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBindersAux(lean_object* v_combinator_290_, lean_object* v_idents_291_, lean_object* v_type_x3f_292_, lean_object* v_body_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = lean_array_get_size(v_idents_291_);
v___x_297_ = l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg(v_combinator_290_, v_idents_291_, v_type_x3f_292_, v___x_296_, v_body_293_, v_a_294_, v_a_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBindersAux___boxed(lean_object* v_combinator_298_, lean_object* v_idents_299_, lean_object* v_type_x3f_300_, lean_object* v_body_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_expandExplicitBindersAux(v_combinator_298_, v_idents_299_, v_type_x3f_300_, v_body_301_, v_a_302_, v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec_ref(v_idents_299_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg(lean_object* v_combinator_305_, lean_object* v_binders_306_, lean_object* v_i_307_, lean_object* v_acc_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_zero_311_; uint8_t v_isZero_312_; 
v_zero_311_ = lean_unsigned_to_nat(0u);
v_isZero_312_ = lean_nat_dec_eq(v_i_307_, v_zero_311_);
if (v_isZero_312_ == 1)
{
lean_object* v___x_313_; 
lean_dec(v_i_307_);
lean_dec(v_combinator_305_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v_acc_308_);
lean_ctor_set(v___x_313_, 1, v_a_310_);
return v___x_313_;
}
else
{
lean_object* v_one_314_; lean_object* v_n_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_idents_318_; lean_object* v___x_319_; lean_object* v_type_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_a_323_; lean_object* v_a_324_; 
v_one_314_ = lean_unsigned_to_nat(1u);
v_n_315_ = lean_nat_sub(v_i_307_, v_one_314_);
lean_dec(v_i_307_);
v___x_316_ = lean_array_fget_borrowed(v_binders_306_, v_n_315_);
v___x_317_ = l_Lean_Syntax_getArg(v___x_316_, v_one_314_);
v_idents_318_ = l_Lean_Syntax_getArgs(v___x_317_);
lean_dec(v___x_317_);
v___x_319_ = lean_unsigned_to_nat(3u);
v_type_320_ = l_Lean_Syntax_getArg(v___x_316_, v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v_type_320_);
lean_inc(v_combinator_305_);
v___x_322_ = l_Lean_expandExplicitBindersAux(v_combinator_305_, v_idents_318_, v___x_321_, v_acc_308_, v_a_309_, v_a_310_);
lean_dec_ref(v_idents_318_);
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
v_a_324_ = lean_ctor_get(v___x_322_, 1);
lean_inc(v_a_324_);
lean_dec_ref(v___x_322_);
v_i_307_ = v_n_315_;
v_acc_308_ = v_a_323_;
v_a_310_ = v_a_324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg___boxed(lean_object* v_combinator_326_, lean_object* v_binders_327_, lean_object* v_i_328_, lean_object* v_acc_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg(v_combinator_326_, v_binders_327_, v_i_328_, v_acc_329_, v_a_330_, v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec_ref(v_binders_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop(lean_object* v_combinator_333_, lean_object* v_binders_334_, lean_object* v_i_335_, lean_object* v_h_336_, lean_object* v_acc_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg(v_combinator_333_, v_binders_334_, v_i_335_, v_acc_337_, v_a_338_, v_a_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___boxed(lean_object* v_combinator_341_, lean_object* v_binders_342_, lean_object* v_i_343_, lean_object* v_h_344_, lean_object* v_acc_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop(v_combinator_341_, v_binders_342_, v_i_343_, v_h_344_, v_acc_345_, v_a_346_, v_a_347_);
lean_dec_ref(v_a_346_);
lean_dec_ref(v_binders_342_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBindersAux(lean_object* v_combinator_349_, lean_object* v_binders_350_, lean_object* v_body_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_array_get_size(v_binders_350_);
v___x_355_ = l___private_Init_NotationExtra_0__Lean_expandBracketedBindersAux_loop___redArg(v_combinator_349_, v_binders_350_, v___x_354_, v_body_351_, v_a_352_, v_a_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBindersAux___boxed(lean_object* v_combinator_356_, lean_object* v_binders_357_, lean_object* v_body_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_expandBracketedBindersAux(v_combinator_356_, v_binders_357_, v_body_358_, v_a_359_, v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec_ref(v_binders_357_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(uint8_t v___x_362_, lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_){
_start:
{
uint8_t v___x_366_; 
v___x_366_ = lean_usize_dec_eq(v_i_364_, v_stop_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_367_ = 1;
v___x_368_ = lean_array_uget_borrowed(v_as_363_, v_i_364_);
lean_inc(v___x_368_);
v___x_369_ = l_Lean_Syntax_getKind(v___x_368_);
v___x_370_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_371_ = lean_name_eq(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v___x_371_ == 0)
{
return v___x_367_;
}
else
{
if (v___x_362_ == 0)
{
size_t v___x_372_; size_t v___x_373_; 
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_add(v_i_364_, v___x_372_);
v_i_364_ = v___x_373_;
goto _start;
}
else
{
return v___x_367_;
}
}
}
else
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0___boxed(lean_object* v___x_376_, lean_object* v_as_377_, lean_object* v_i_378_, lean_object* v_stop_379_){
_start:
{
uint8_t v___x_1122__boxed_380_; size_t v_i_boxed_381_; size_t v_stop_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v___x_1122__boxed_380_ = lean_unbox(v___x_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_stop_boxed_382_ = lean_unbox_usize(v_stop_379_);
lean_dec(v_stop_379_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_1122__boxed_380_, v_as_377_, v_i_boxed_381_, v_stop_boxed_382_);
lean_dec_ref(v_as_377_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders(lean_object* v_combinatorDeclName_386_, lean_object* v_explicitBinders_387_, lean_object* v_body_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_ref_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_ref_391_ = lean_ctor_get(v_a_389_, 5);
v___x_392_ = 0;
v___x_393_ = l_Lean_mkCIdentFrom(v_ref_391_, v_combinatorDeclName_386_, v___x_392_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_Lean_Syntax_getArg(v_explicitBinders_387_, v___x_394_);
lean_inc(v___x_395_);
v___x_396_ = l_Lean_Syntax_getKind(v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_398_ = lean_name_eq(v___x_396_, v___x_397_);
lean_dec(v___x_396_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = l_Lean_Syntax_getArgs(v___x_395_);
lean_dec(v___x_395_);
v___x_400_ = lean_array_get_size(v___x_399_);
v___x_401_ = lean_nat_dec_lt(v___x_394_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_expandBracketedBindersAux(v___x_393_, v___x_399_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_399_);
return v___x_402_;
}
else
{
if (v___x_401_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_expandBracketedBindersAux(v___x_393_, v___x_399_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_399_);
return v___x_403_;
}
else
{
size_t v___x_404_; size_t v___x_405_; uint8_t v___x_406_; 
v___x_404_ = ((size_t)0ULL);
v___x_405_ = lean_usize_of_nat(v___x_400_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_398_, v___x_399_, v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_expandBracketedBindersAux(v___x_393_, v___x_399_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_399_);
return v___x_407_;
}
else
{
if (v___x_398_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_399_);
lean_dec(v___x_393_);
lean_dec(v_body_388_);
v___x_408_ = ((lean_object*)(l_Lean_expandExplicitBinders___closed__0));
v___x_409_ = l_Lean_Macro_throwError___redArg(v___x_408_, v_a_389_, v_a_390_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = l_Lean_expandBracketedBindersAux(v___x_393_, v___x_399_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_399_);
return v___x_410_;
}
}
}
}
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_411_ = l_Lean_Syntax_getArg(v___x_395_, v___x_394_);
v___x_412_ = l_Lean_Syntax_getArgs(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = l_Lean_Syntax_getArg(v___x_395_, v___x_413_);
lean_dec(v___x_395_);
v___x_415_ = l_Lean_Syntax_isNone(v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = l_Lean_Syntax_getArg(v___x_414_, v___x_413_);
lean_dec(v___x_414_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = l_Lean_expandExplicitBindersAux(v___x_393_, v___x_412_, v___x_417_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_412_);
return v___x_418_;
}
else
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v___x_414_);
v___x_419_ = lean_box(0);
v___x_420_ = l_Lean_expandExplicitBindersAux(v___x_393_, v___x_412_, v___x_419_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_412_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders___boxed(lean_object* v_combinatorDeclName_421_, lean_object* v_explicitBinders_422_, lean_object* v_body_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_expandExplicitBinders(v_combinatorDeclName_421_, v_explicitBinders_422_, v_body_423_, v_a_424_, v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_explicitBinders_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders(lean_object* v_combinatorDeclName_427_, lean_object* v_bracketedExplicitBinders_428_, lean_object* v_body_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_ref_432_; uint8_t v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_ref_432_ = lean_ctor_get(v_a_430_, 5);
v___x_433_ = 0;
v___x_434_ = l_Lean_mkCIdentFrom(v_ref_432_, v_combinatorDeclName_427_, v___x_433_);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_mk_empty_array_with_capacity(v___x_435_);
v___x_437_ = lean_array_push(v___x_436_, v_bracketedExplicitBinders_428_);
v___x_438_ = l_Lean_expandBracketedBindersAux(v___x_434_, v___x_437_, v_body_429_, v_a_430_, v_a_431_);
lean_dec_ref(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders___boxed(lean_object* v_combinatorDeclName_439_, lean_object* v_bracketedExplicitBinders_440_, lean_object* v_body_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_expandBracketedBinders(v_combinatorDeclName_439_, v_bracketedExplicitBinders_440_, v_body_441_, v_a_442_, v_a_443_);
lean_dec_ref(v_a_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(lean_object* v_____do__lift_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = 0;
v___x_652_ = l_Lean_SourceInfo_fromRef(v_____do__lift_648_, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___y_650_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0___boxed(lean_object* v_____do__lift_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_____do__lift_654_, v___y_655_, v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v_____do__lift_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(size_t v_sz_658_, size_t v_i_659_, lean_object* v_bs_660_){
_start:
{
uint8_t v___x_661_; 
v___x_661_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; 
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_bs_660_);
return v___x_662_;
}
else
{
lean_object* v_v_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_v_663_ = lean_array_uget_borrowed(v_bs_660_, v_i_659_);
v___x_664_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__1));
lean_inc(v_v_663_);
v___x_665_ = l_Lean_Syntax_isOfKind(v_v_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; 
lean_dec_ref(v_bs_660_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = l_Lean_Syntax_getArg(v_v_663_, v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_668_);
v___x_670_ = l_Lean_Syntax_isOfKind(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; 
lean_dec(v___x_668_);
lean_dec_ref(v_bs_660_);
v___x_671_ = lean_box(0);
return v___x_671_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = l_Lean_Syntax_getArg(v_v_663_, v___x_672_);
v___x_674_ = l_Lean_Syntax_matchesNull(v___x_673_, v___x_667_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec(v___x_668_);
lean_dec_ref(v_bs_660_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v___x_676_; lean_object* v_bs_x27_677_; lean_object* v_cs_u2081_678_; lean_object* v_cs_u2082_679_; lean_object* v___x_680_; size_t v___x_681_; size_t v___x_682_; lean_object* v___x_683_; 
v___x_676_ = lean_unsigned_to_nat(2u);
v_bs_x27_677_ = lean_array_uset(v_bs_660_, v_i_659_, v___x_667_);
v_cs_u2081_678_ = l_Lean_Syntax_getArg(v___x_668_, v___x_667_);
v_cs_u2082_679_ = l_Lean_Syntax_getArg(v___x_668_, v___x_676_);
lean_dec(v___x_668_);
v___x_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_680_, 0, v_cs_u2081_678_);
lean_ctor_set(v___x_680_, 1, v_cs_u2082_679_);
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_659_, v___x_681_);
v___x_683_ = lean_array_uset(v_bs_x27_677_, v_i_659_, v___x_680_);
v_i_659_ = v___x_682_;
v_bs_660_ = v___x_683_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0___boxed(lean_object* v_sz_685_, lean_object* v_i_686_, lean_object* v_bs_687_){
_start:
{
size_t v_sz_boxed_688_; size_t v_i_boxed_689_; lean_object* v_res_690_; 
v_sz_boxed_688_ = lean_unbox_usize(v_sz_685_);
lean_dec(v_sz_685_);
v_i_boxed_689_ = lean_unbox_usize(v_i_686_);
lean_dec(v_i_686_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_boxed_688_, v_i_boxed_689_, v_bs_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(lean_object* v_as_702_, size_t v_sz_703_, size_t v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
uint8_t v___x_708_; 
v___x_708_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; 
v___x_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_709_, 0, v_b_705_);
lean_ctor_set(v___x_709_, 1, v___y_707_);
return v___x_709_;
}
else
{
lean_object* v_a_710_; lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_732_; 
v_a_710_ = lean_array_uget(v_as_702_, v_i_704_);
v_fst_711_ = lean_ctor_get(v_a_710_, 0);
v_snd_712_ = lean_ctor_get(v_a_710_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_710_);
if (v_isSharedCheck_732_ == 0)
{
v___x_714_ = v_a_710_;
v_isShared_715_ = v_isSharedCheck_732_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_inc(v_fst_711_);
lean_dec(v_a_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_732_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_ref_716_; uint8_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v_ref_716_ = lean_ctor_get(v___y_706_, 5);
v___x_717_ = 0;
v___x_718_ = l_Lean_SourceInfo_fromRef(v_ref_716_, v___x_717_);
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1));
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v___x_718_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 2);
lean_ctor_set(v___x_714_, 1, v___x_721_);
lean_ctor_set(v___x_714_, 0, v___x_718_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_721_);
v___x_723_ = v_reuseFailAlloc_731_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; size_t v___x_728_; size_t v___x_729_; 
lean_inc_n(v___x_718_, 2);
v___x_724_ = l_Lean_Syntax_node3(v___x_718_, v___x_720_, v_fst_711_, v___x_723_, v_snd_712_);
v___x_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5));
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_718_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Lean_Syntax_node3(v___x_718_, v___x_719_, v___x_724_, v___x_726_, v_b_705_);
v___x_728_ = ((size_t)1ULL);
v___x_729_ = lean_usize_add(v_i_704_, v___x_728_);
v_i_704_ = v___x_729_;
v_b_705_ = v___x_727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___boxed(lean_object* v_as_733_, lean_object* v_sz_734_, lean_object* v_i_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_sz_boxed_739_ = lean_unbox_usize(v_sz_734_);
lean_dec(v_sz_734_);
v_i_boxed_740_ = lean_unbox_usize(v_i_735_);
lean_dec(v_i_735_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v_as_733_, v_sz_boxed_739_, v_i_boxed_740_, v_b_736_, v___y_737_, v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec_ref(v_as_733_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(size_t v_sz_742_, size_t v_i_743_, lean_object* v_bs_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_743_, v_sz_742_);
if (v___x_745_ == 0)
{
return v_bs_744_;
}
else
{
lean_object* v_v_746_; lean_object* v___x_747_; lean_object* v_bs_x27_748_; size_t v___x_749_; size_t v___x_750_; lean_object* v___x_751_; 
v_v_746_ = lean_array_uget(v_bs_744_, v_i_743_);
v___x_747_ = lean_unsigned_to_nat(0u);
v_bs_x27_748_ = lean_array_uset(v_bs_744_, v_i_743_, v___x_747_);
v___x_749_ = ((size_t)1ULL);
v___x_750_ = lean_usize_add(v_i_743_, v___x_749_);
v___x_751_ = lean_array_uset(v_bs_x27_748_, v_i_743_, v_v_746_);
v_i_743_ = v___x_750_;
v_bs_744_ = v___x_751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5___boxed(lean_object* v_sz_753_, lean_object* v_i_754_, lean_object* v_bs_755_){
_start:
{
size_t v_sz_boxed_756_; size_t v_i_boxed_757_; lean_object* v_res_758_; 
v_sz_boxed_756_ = lean_unbox_usize(v_sz_753_);
lean_dec(v_sz_753_);
v_i_boxed_757_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_boxed_756_, v_i_boxed_757_, v_bs_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(size_t v_sz_759_, size_t v_i_760_, lean_object* v_bs_761_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = lean_usize_dec_lt(v_i_760_, v_sz_759_);
if (v___x_762_ == 0)
{
return v_bs_761_;
}
else
{
lean_object* v_v_763_; lean_object* v___x_764_; lean_object* v_bs_x27_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v_v_763_ = lean_array_uget(v_bs_761_, v_i_760_);
v___x_764_ = lean_unsigned_to_nat(0u);
v_bs_x27_765_ = lean_array_uset(v_bs_761_, v_i_760_, v___x_764_);
v___x_766_ = ((size_t)1ULL);
v___x_767_ = lean_usize_add(v_i_760_, v___x_766_);
v___x_768_ = lean_array_uset(v_bs_x27_765_, v_i_760_, v_v_763_);
v_i_760_ = v___x_767_;
v_bs_761_ = v___x_768_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4___boxed(lean_object* v_sz_770_, lean_object* v_i_771_, lean_object* v_bs_772_){
_start:
{
size_t v_sz_boxed_773_; size_t v_i_boxed_774_; lean_object* v_res_775_; 
v_sz_boxed_773_ = lean_unbox_usize(v_sz_770_);
lean_dec(v_sz_770_);
v_i_boxed_774_ = lean_unbox_usize(v_i_771_);
lean_dec(v_i_771_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_boxed_773_, v_i_boxed_774_, v_bs_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(size_t v_sz_776_, size_t v_i_777_, lean_object* v_bs_778_){
_start:
{
uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_lt(v_i_777_, v_sz_776_);
if (v___x_779_ == 0)
{
return v_bs_778_;
}
else
{
lean_object* v_v_780_; lean_object* v_fst_781_; lean_object* v___x_782_; lean_object* v_bs_x27_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v_v_780_ = lean_array_uget_borrowed(v_bs_778_, v_i_777_);
v_fst_781_ = lean_ctor_get(v_v_780_, 0);
lean_inc(v_fst_781_);
v___x_782_ = lean_unsigned_to_nat(0u);
v_bs_x27_783_ = lean_array_uset(v_bs_778_, v_i_777_, v___x_782_);
v___x_784_ = ((size_t)1ULL);
v___x_785_ = lean_usize_add(v_i_777_, v___x_784_);
v___x_786_ = lean_array_uset(v_bs_x27_783_, v_i_777_, v_fst_781_);
v_i_777_ = v___x_785_;
v_bs_778_ = v___x_786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2___boxed(lean_object* v_sz_788_, lean_object* v_i_789_, lean_object* v_bs_790_){
_start:
{
size_t v_sz_boxed_791_; size_t v_i_boxed_792_; lean_object* v_res_793_; 
v_sz_boxed_791_ = lean_unbox_usize(v_sz_788_);
lean_dec(v_sz_788_);
v_i_boxed_792_ = lean_unbox_usize(v_i_789_);
lean_dec(v_i_789_);
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_boxed_791_, v_i_boxed_792_, v_bs_790_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(size_t v_sz_794_, size_t v_i_795_, lean_object* v_bs_796_){
_start:
{
uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_797_ == 0)
{
return v_bs_796_;
}
else
{
lean_object* v_v_798_; lean_object* v_snd_799_; lean_object* v___x_800_; lean_object* v_bs_x27_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v_v_798_ = lean_array_uget_borrowed(v_bs_796_, v_i_795_);
v_snd_799_ = lean_ctor_get(v_v_798_, 1);
lean_inc(v_snd_799_);
v___x_800_ = lean_unsigned_to_nat(0u);
v_bs_x27_801_ = lean_array_uset(v_bs_796_, v_i_795_, v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_795_, v___x_802_);
v___x_804_ = lean_array_uset(v_bs_x27_801_, v_i_795_, v_snd_799_);
v_i_795_ = v___x_803_;
v_bs_796_ = v___x_804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1___boxed(lean_object* v_sz_806_, lean_object* v_i_807_, lean_object* v_bs_808_){
_start:
{
size_t v_sz_boxed_809_; size_t v_i_boxed_810_; lean_object* v_res_811_; 
v_sz_boxed_809_ = lean_unbox_usize(v_sz_806_);
lean_dec(v_sz_806_);
v_i_boxed_810_ = lean_unbox_usize(v_i_807_);
lean_dec(v_i_807_);
v_res_811_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_boxed_809_, v_i_boxed_810_, v_bs_808_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14));
v___x_829_ = l_String_toRawSubstring_x27(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18));
v___x_835_ = l_String_toRawSubstring_x27(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27));
v___x_846_ = l_String_toRawSubstring_x27(v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(lean_object* v_x_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v___x_868_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_869_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1));
lean_inc(v_x_865_);
v___x_870_ = l_Lean_Syntax_isOfKind(v_x_865_, v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec(v_x_865_);
v___x_871_ = lean_box(1);
v___x_872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_a_867_);
return v___x_872_;
}
else
{
lean_object* v___x_873_; lean_object* v___y_875_; lean_object* v___y_876_; size_t v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_940_; size_t v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_1007_; size_t v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; size_t v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; size_t v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; size_t v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1271_; lean_object* v___y_1272_; size_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; size_t v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; size_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v_doc_x3f_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___x_1555_; uint8_t v___x_1556_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_1555_ = l_Lean_Syntax_getArg(v_x_865_, v___x_873_);
v___x_1556_ = l_Lean_Syntax_isNone(v___x_1555_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1557_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1555_);
v___x_1558_ = l_Lean_Syntax_matchesNull(v___x_1555_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec(v___x_1555_);
lean_dec(v_x_865_);
v___x_1559_ = lean_box(1);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v_a_867_);
return v___x_1560_;
}
else
{
lean_object* v_doc_x3f_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_doc_x3f_1561_ = l_Lean_Syntax_getArg(v___x_1555_, v___x_873_);
lean_dec(v___x_1555_);
v___x_1562_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36));
lean_inc(v_doc_x3f_1561_);
v___x_1563_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1561_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec(v_doc_x3f_1561_);
lean_dec(v_x_865_);
v___x_1564_ = lean_box(1);
v___x_1565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
lean_ctor_set(v___x_1565_, 1, v_a_867_);
return v___x_1565_;
}
else
{
lean_object* v___x_1566_; 
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_doc_x3f_1561_);
v_doc_x3f_1508_ = v___x_1566_;
v___y_1509_ = v_a_866_;
v___y_1510_ = v_a_867_;
goto v___jp_1507_;
}
}
}
else
{
lean_object* v___x_1567_; 
lean_dec(v___x_1555_);
v___x_1567_ = lean_box(0);
v_doc_x3f_1508_ = v___x_1567_;
v___y_1509_ = v_a_866_;
v___y_1510_ = v_a_867_;
goto v___jp_1507_;
}
v___jp_874_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; size_t v_sz_903_; lean_object* v___x_904_; size_t v_sz_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_893_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_894_ = lean_box(2);
lean_inc_n(v___y_884_, 4);
v___x_895_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___y_884_);
lean_ctor_set(v___x_895_, 2, v___x_893_);
v___x_896_ = lean_mk_empty_array_with_capacity(v___y_881_);
v___x_897_ = lean_array_push(v___x_896_, v___y_892_);
v___x_898_ = lean_array_push(v___x_897_, v___x_895_);
v___x_899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_899_, 0, v___x_894_);
lean_ctor_set(v___x_899_, 1, v___y_891_);
lean_ctor_set(v___x_899_, 2, v___x_898_);
v___x_900_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_890_);
lean_inc_ref_n(v___y_882_, 6);
v___x_901_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___y_890_, v___x_900_);
v___x_902_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_903_ = lean_array_size(v___y_888_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_903_, v___y_877_, v___y_888_);
v_sz_905_ = lean_array_size(v___x_904_);
v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_905_, v___y_877_, v___x_904_);
lean_inc_ref(v___y_876_);
v___x_907_ = l_Array_append___redArg(v___y_876_, v___x_906_);
lean_dec_ref(v___x_906_);
lean_inc_n(v___y_885_, 14);
v___x_908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_908_, 0, v___y_885_);
lean_ctor_set(v___x_908_, 1, v___y_884_);
lean_ctor_set(v___x_908_, 2, v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_886_, 2);
v___x_910_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___y_886_, v___x_909_);
v___x_911_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_912_, 0, v___y_885_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_914_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___y_886_, v___x_913_);
v___x_915_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___y_885_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_918_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___x_917_, v___x_902_);
v___x_919_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___y_885_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_Syntax_node1(v___y_885_, v___x_918_, v___x_920_);
v___x_922_ = l_Lean_Syntax_node1(v___y_885_, v___y_884_, v___x_921_);
v___x_923_ = l_Lean_Syntax_node2(v___y_885_, v___x_914_, v___x_916_, v___x_922_);
v___x_924_ = l_Lean_Syntax_node2(v___y_885_, v___x_910_, v___x_912_, v___x_923_);
v___x_925_ = l_Lean_Syntax_node1(v___y_885_, v___y_884_, v___x_924_);
v___x_926_ = l_Lean_Syntax_node2(v___y_885_, v___x_901_, v___x_908_, v___x_925_);
v___x_927_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_928_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___y_890_, v___x_927_);
v___x_929_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_930_, 0, v___y_885_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
v___x_931_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_932_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_933_ = l_Lean_Name_mkStr4(v___x_868_, v___y_882_, v___x_931_, v___x_932_);
lean_inc_n(v___y_887_, 3);
v___x_934_ = l_Lean_Syntax_node2(v___y_885_, v___x_933_, v___y_887_, v___y_887_);
v___x_935_ = l_Lean_Syntax_node4(v___y_885_, v___x_928_, v___x_930_, v___y_878_, v___x_934_, v___y_887_);
v___x_936_ = l_Lean_Syntax_node5(v___y_885_, v___y_880_, v___y_883_, v___x_899_, v___x_926_, v___x_935_, v___y_887_);
v___x_937_ = l_Lean_Syntax_node2(v___y_885_, v___y_889_, v___y_875_, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___y_879_);
return v___x_938_;
}
v___jp_939_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref_n(v___y_940_, 2);
v___x_961_ = l_Array_append___redArg(v___y_940_, v___y_960_);
lean_dec_ref(v___y_960_);
lean_inc_n(v___y_952_, 5);
lean_inc_n(v___y_954_, 20);
v___x_962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_962_, 0, v___y_954_);
lean_ctor_set(v___x_962_, 1, v___y_952_);
lean_ctor_set(v___x_962_, 2, v___x_961_);
v___x_963_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_955_, 2);
lean_inc_ref_n(v___y_949_, 6);
v___x_964_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___y_955_, v___x_963_);
v___x_965_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___y_954_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_968_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___y_955_, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_970_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_971_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___x_969_, v___x_970_);
v___x_972_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_973_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_944_);
lean_inc(v___y_951_);
v___x_974_ = l_Lean_addMacroScope(v___y_951_, v___x_973_, v___y_944_);
lean_inc_n(v___y_950_, 2);
v___x_975_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_975_, 0, v___y_954_);
lean_ctor_set(v___x_975_, 1, v___x_972_);
lean_ctor_set(v___x_975_, 2, v___x_974_);
lean_ctor_set(v___x_975_, 3, v___y_950_);
v___x_976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_976_, 0, v___y_954_);
lean_ctor_set(v___x_976_, 1, v___y_952_);
lean_ctor_set(v___x_976_, 2, v___y_940_);
lean_inc_ref_n(v___x_976_, 7);
lean_inc(v___x_971_);
v___x_977_ = l_Lean_Syntax_node2(v___y_954_, v___x_971_, v___x_975_, v___x_976_);
lean_inc(v___x_968_);
v___x_978_ = l_Lean_Syntax_node2(v___y_954_, v___x_968_, v___y_947_, v___x_977_);
v___x_979_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_980_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_980_, 0, v___y_954_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
lean_inc(v___y_957_);
v___x_981_ = l_Lean_Syntax_node1(v___y_954_, v___y_957_, v___x_976_);
v___x_982_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_983_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_984_ = l_Lean_addMacroScope(v___y_951_, v___x_983_, v___y_944_);
v___x_985_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_985_, 0, v___y_954_);
lean_ctor_set(v___x_985_, 1, v___x_982_);
lean_ctor_set(v___x_985_, 2, v___x_984_);
lean_ctor_set(v___x_985_, 3, v___y_950_);
v___x_986_ = l_Lean_Syntax_node2(v___y_954_, v___x_971_, v___x_985_, v___x_976_);
v___x_987_ = l_Lean_Syntax_node2(v___y_954_, v___x_968_, v___x_981_, v___x_986_);
v___x_988_ = l_Lean_Syntax_node3(v___y_954_, v___y_952_, v___x_978_, v___x_980_, v___x_987_);
v___x_989_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___y_954_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l_Lean_Syntax_node3(v___y_954_, v___x_964_, v___x_966_, v___x_988_, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___y_954_, v___y_952_, v___x_991_);
v___x_993_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_959_, 3);
v___x_994_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___y_959_, v___x_993_);
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___y_954_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
v___x_996_ = l_Lean_Syntax_node1(v___y_954_, v___x_994_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node1(v___y_954_, v___y_952_, v___x_996_);
v___x_998_ = l_Lean_Syntax_node7(v___y_954_, v___y_945_, v___x_962_, v___x_992_, v___x_997_, v___x_976_, v___x_976_, v___x_976_, v___x_976_);
v___x_999_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1000_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___y_959_, v___x_999_);
v___x_1001_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_954_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1004_ = l_Lean_Name_mkStr4(v___x_868_, v___y_949_, v___y_959_, v___x_1003_);
if (lean_obj_tag(v___y_953_) == 0)
{
v___y_875_ = v___x_998_;
v___y_876_ = v___y_940_;
v___y_877_ = v___y_941_;
v___y_878_ = v___y_943_;
v___y_879_ = v___y_946_;
v___y_880_ = v___x_1000_;
v___y_881_ = v___y_948_;
v___y_882_ = v___y_949_;
v___y_883_ = v___x_1002_;
v___y_884_ = v___y_952_;
v___y_885_ = v___y_954_;
v___y_886_ = v___y_955_;
v___y_887_ = v___x_976_;
v___y_888_ = v___y_956_;
v___y_889_ = v___y_958_;
v___y_890_ = v___y_959_;
v___y_891_ = v___x_1004_;
v___y_892_ = v___y_942_;
goto v___jp_874_;
}
else
{
lean_object* v_val_1005_; 
lean_dec(v___y_942_);
v_val_1005_ = lean_ctor_get(v___y_953_, 0);
lean_inc(v_val_1005_);
lean_dec_ref(v___y_953_);
v___y_875_ = v___x_998_;
v___y_876_ = v___y_940_;
v___y_877_ = v___y_941_;
v___y_878_ = v___y_943_;
v___y_879_ = v___y_946_;
v___y_880_ = v___x_1000_;
v___y_881_ = v___y_948_;
v___y_882_ = v___y_949_;
v___y_883_ = v___x_1002_;
v___y_884_ = v___y_952_;
v___y_885_ = v___y_954_;
v___y_886_ = v___y_955_;
v___y_887_ = v___x_976_;
v___y_888_ = v___y_956_;
v___y_889_ = v___y_958_;
v___y_890_ = v___y_959_;
v___y_891_ = v___x_1004_;
v___y_892_ = v_val_1005_;
goto v___jp_874_;
}
}
v___jp_1006_:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; lean_object* v___x_1036_; size_t v_sz_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1025_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1026_ = lean_box(2);
lean_inc_n(v___y_1015_, 4);
v___x_1027_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___y_1015_);
lean_ctor_set(v___x_1027_, 2, v___x_1025_);
v___x_1028_ = lean_mk_empty_array_with_capacity(v___y_1014_);
v___x_1029_ = lean_array_push(v___x_1028_, v___y_1024_);
v___x_1030_ = lean_array_push(v___x_1029_, v___x_1027_);
v___x_1031_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1026_);
lean_ctor_set(v___x_1031_, 1, v___y_1017_);
lean_ctor_set(v___x_1031_, 2, v___x_1030_);
v___x_1032_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1023_);
lean_inc_ref_n(v___y_1016_, 6);
v___x_1033_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___y_1023_, v___x_1032_);
v___x_1034_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1035_ = lean_array_size(v___y_1021_);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1035_, v___y_1008_, v___y_1021_);
v_sz_1037_ = lean_array_size(v___x_1036_);
v___x_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1037_, v___y_1008_, v___x_1036_);
lean_inc_ref(v___y_1013_);
v___x_1039_ = l_Array_append___redArg(v___y_1013_, v___x_1038_);
lean_dec_ref(v___x_1038_);
lean_inc_n(v___y_1019_, 14);
v___x_1040_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1040_, 0, v___y_1019_);
lean_ctor_set(v___x_1040_, 1, v___y_1015_);
lean_ctor_set(v___x_1040_, 2, v___x_1039_);
v___x_1041_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1020_, 2);
v___x_1042_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___y_1020_, v___x_1041_);
v___x_1043_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___y_1019_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1046_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___y_1020_, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1048_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___y_1019_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1050_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___x_1049_, v___x_1034_);
v___x_1051_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___y_1019_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node1(v___y_1019_, v___x_1050_, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node1(v___y_1019_, v___y_1015_, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_node2(v___y_1019_, v___x_1046_, v___x_1048_, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node2(v___y_1019_, v___x_1042_, v___x_1044_, v___x_1055_);
v___x_1057_ = l_Lean_Syntax_node1(v___y_1019_, v___y_1015_, v___x_1056_);
v___x_1058_ = l_Lean_Syntax_node2(v___y_1019_, v___x_1033_, v___x_1040_, v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1060_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___y_1023_, v___x_1059_);
v___x_1061_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1062_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___y_1019_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1064_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1065_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1016_, v___x_1063_, v___x_1064_);
lean_inc_n(v___y_1010_, 3);
v___x_1066_ = l_Lean_Syntax_node2(v___y_1019_, v___x_1065_, v___y_1010_, v___y_1010_);
v___x_1067_ = l_Lean_Syntax_node4(v___y_1019_, v___x_1060_, v___x_1062_, v___y_1009_, v___x_1066_, v___y_1010_);
v___x_1068_ = l_Lean_Syntax_node5(v___y_1019_, v___y_1007_, v___y_1012_, v___x_1031_, v___x_1058_, v___x_1067_, v___y_1010_);
v___x_1069_ = l_Lean_Syntax_node2(v___y_1019_, v___y_1018_, v___y_1022_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___y_1011_);
return v___x_1070_;
}
v___jp_1071_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_inc_ref_n(v___y_1078_, 2);
v___x_1093_ = l_Array_append___redArg(v___y_1078_, v___y_1092_);
lean_dec_ref(v___y_1092_);
lean_inc_n(v___y_1080_, 5);
lean_inc_n(v___y_1087_, 20);
v___x_1094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1094_, 0, v___y_1087_);
lean_ctor_set(v___x_1094_, 1, v___y_1080_);
lean_ctor_set(v___x_1094_, 2, v___x_1093_);
v___x_1095_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1088_, 2);
lean_inc_ref_n(v___y_1081_, 6);
v___x_1096_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___y_1088_, v___x_1095_);
v___x_1097_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1098_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___y_1087_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1100_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___y_1088_, v___x_1099_);
v___x_1101_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1102_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1103_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___x_1101_, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1105_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_1076_);
lean_inc(v___y_1084_);
v___x_1106_ = l_Lean_addMacroScope(v___y_1084_, v___x_1105_, v___y_1076_);
lean_inc_n(v___y_1082_, 2);
v___x_1107_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1087_);
lean_ctor_set(v___x_1107_, 1, v___x_1104_);
lean_ctor_set(v___x_1107_, 2, v___x_1106_);
lean_ctor_set(v___x_1107_, 3, v___y_1082_);
v___x_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___y_1087_);
lean_ctor_set(v___x_1108_, 1, v___y_1080_);
lean_ctor_set(v___x_1108_, 2, v___y_1078_);
lean_inc_ref_n(v___x_1108_, 7);
lean_inc(v___x_1103_);
v___x_1109_ = l_Lean_Syntax_node2(v___y_1087_, v___x_1103_, v___x_1107_, v___x_1108_);
lean_inc(v___x_1100_);
v___x_1110_ = l_Lean_Syntax_node2(v___y_1087_, v___x_1100_, v___y_1077_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___y_1087_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
lean_inc(v___y_1090_);
v___x_1113_ = l_Lean_Syntax_node1(v___y_1087_, v___y_1090_, v___x_1108_);
v___x_1114_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_1115_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_1116_ = l_Lean_addMacroScope(v___y_1084_, v___x_1115_, v___y_1076_);
v___x_1117_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1117_, 0, v___y_1087_);
lean_ctor_set(v___x_1117_, 1, v___x_1114_);
lean_ctor_set(v___x_1117_, 2, v___x_1116_);
lean_ctor_set(v___x_1117_, 3, v___y_1082_);
v___x_1118_ = l_Lean_Syntax_node2(v___y_1087_, v___x_1103_, v___x_1117_, v___x_1108_);
v___x_1119_ = l_Lean_Syntax_node2(v___y_1087_, v___x_1100_, v___x_1113_, v___x_1118_);
v___x_1120_ = l_Lean_Syntax_node3(v___y_1087_, v___y_1080_, v___x_1110_, v___x_1112_, v___x_1119_);
v___x_1121_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___y_1087_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node3(v___y_1087_, v___x_1096_, v___x_1098_, v___x_1120_, v___x_1122_);
v___x_1124_ = l_Lean_Syntax_node1(v___y_1087_, v___y_1080_, v___x_1123_);
v___x_1125_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_1091_, 3);
v___x_1126_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___y_1091_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___y_1087_);
lean_ctor_set(v___x_1127_, 1, v___x_1125_);
v___x_1128_ = l_Lean_Syntax_node1(v___y_1087_, v___x_1126_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node1(v___y_1087_, v___y_1080_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node7(v___y_1087_, v___y_1083_, v___x_1094_, v___x_1124_, v___x_1129_, v___x_1108_, v___x_1108_, v___x_1108_, v___x_1108_);
v___x_1131_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1132_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___y_1091_, v___x_1131_);
v___x_1133_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1087_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1136_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1081_, v___y_1091_, v___x_1135_);
if (lean_obj_tag(v___y_1086_) == 0)
{
v___y_1007_ = v___x_1132_;
v___y_1008_ = v___y_1072_;
v___y_1009_ = v___y_1074_;
v___y_1010_ = v___x_1108_;
v___y_1011_ = v___y_1075_;
v___y_1012_ = v___x_1134_;
v___y_1013_ = v___y_1078_;
v___y_1014_ = v___y_1079_;
v___y_1015_ = v___y_1080_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___x_1136_;
v___y_1018_ = v___y_1085_;
v___y_1019_ = v___y_1087_;
v___y_1020_ = v___y_1088_;
v___y_1021_ = v___y_1089_;
v___y_1022_ = v___x_1130_;
v___y_1023_ = v___y_1091_;
v___y_1024_ = v___y_1073_;
goto v___jp_1006_;
}
else
{
lean_object* v_val_1137_; 
lean_dec(v___y_1073_);
v_val_1137_ = lean_ctor_get(v___y_1086_, 0);
lean_inc(v_val_1137_);
lean_dec_ref(v___y_1086_);
v___y_1007_ = v___x_1132_;
v___y_1008_ = v___y_1072_;
v___y_1009_ = v___y_1074_;
v___y_1010_ = v___x_1108_;
v___y_1011_ = v___y_1075_;
v___y_1012_ = v___x_1134_;
v___y_1013_ = v___y_1078_;
v___y_1014_ = v___y_1079_;
v___y_1015_ = v___y_1080_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___x_1136_;
v___y_1018_ = v___y_1085_;
v___y_1019_ = v___y_1087_;
v___y_1020_ = v___y_1088_;
v___y_1021_ = v___y_1089_;
v___y_1022_ = v___x_1130_;
v___y_1023_ = v___y_1091_;
v___y_1024_ = v_val_1137_;
goto v___jp_1006_;
}
}
v___jp_1138_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; size_t v_sz_1167_; lean_object* v___x_1168_; size_t v_sz_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1157_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1158_ = lean_box(2);
lean_inc_n(v___y_1144_, 4);
v___x_1159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
lean_ctor_set(v___x_1159_, 1, v___y_1144_);
lean_ctor_set(v___x_1159_, 2, v___x_1157_);
v___x_1160_ = lean_mk_empty_array_with_capacity(v___y_1143_);
v___x_1161_ = lean_array_push(v___x_1160_, v___y_1156_);
v___x_1162_ = lean_array_push(v___x_1161_, v___x_1159_);
v___x_1163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1158_);
lean_ctor_set(v___x_1163_, 1, v___y_1150_);
lean_ctor_set(v___x_1163_, 2, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1149_);
lean_inc_ref_n(v___y_1145_, 6);
v___x_1165_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___y_1149_, v___x_1164_);
v___x_1166_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1167_ = lean_array_size(v___y_1154_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1167_, v___y_1139_, v___y_1154_);
v_sz_1169_ = lean_array_size(v___x_1168_);
v___x_1170_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1169_, v___y_1139_, v___x_1168_);
lean_inc_ref(v___y_1141_);
v___x_1171_ = l_Array_append___redArg(v___y_1141_, v___x_1170_);
lean_dec_ref(v___x_1170_);
lean_inc_n(v___y_1152_, 14);
v___x_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1172_, 0, v___y_1152_);
lean_ctor_set(v___x_1172_, 1, v___y_1144_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
v___x_1173_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1153_, 2);
v___x_1174_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___y_1153_, v___x_1173_);
v___x_1175_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___y_1152_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1178_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___y_1153_, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___y_1152_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1182_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___x_1181_, v___x_1166_);
v___x_1183_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___y_1152_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_node1(v___y_1152_, v___x_1182_, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node1(v___y_1152_, v___y_1144_, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_node2(v___y_1152_, v___x_1178_, v___x_1180_, v___x_1186_);
v___x_1188_ = l_Lean_Syntax_node2(v___y_1152_, v___x_1174_, v___x_1176_, v___x_1187_);
v___x_1189_ = l_Lean_Syntax_node1(v___y_1152_, v___y_1144_, v___x_1188_);
v___x_1190_ = l_Lean_Syntax_node2(v___y_1152_, v___x_1165_, v___x_1172_, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1192_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___y_1149_, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___y_1152_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1196_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1197_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1145_, v___x_1195_, v___x_1196_);
lean_inc_n(v___y_1155_, 3);
v___x_1198_ = l_Lean_Syntax_node2(v___y_1152_, v___x_1197_, v___y_1155_, v___y_1155_);
v___x_1199_ = l_Lean_Syntax_node4(v___y_1152_, v___x_1192_, v___x_1194_, v___y_1140_, v___x_1198_, v___y_1155_);
v___x_1200_ = l_Lean_Syntax_node5(v___y_1152_, v___y_1148_, v___y_1146_, v___x_1163_, v___x_1190_, v___x_1199_, v___y_1155_);
v___x_1201_ = l_Lean_Syntax_node2(v___y_1152_, v___y_1151_, v___y_1142_, v___x_1200_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___y_1147_);
return v___x_1202_;
}
v___jp_1203_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_inc_ref_n(v___y_1209_, 2);
v___x_1225_ = l_Array_append___redArg(v___y_1209_, v___y_1224_);
lean_dec_ref(v___y_1224_);
lean_inc_n(v___y_1212_, 5);
lean_inc_n(v___y_1220_, 20);
v___x_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1226_, 0, v___y_1220_);
lean_ctor_set(v___x_1226_, 1, v___y_1212_);
lean_ctor_set(v___x_1226_, 2, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1221_, 2);
lean_inc_ref_n(v___y_1213_, 6);
v___x_1228_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___y_1221_, v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1230_, 0, v___y_1220_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1232_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___y_1221_, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1234_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1235_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___x_1233_, v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1237_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_1208_);
lean_inc(v___y_1215_);
v___x_1238_ = l_Lean_addMacroScope(v___y_1215_, v___x_1237_, v___y_1208_);
lean_inc_n(v___y_1214_, 2);
v___x_1239_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1239_, 0, v___y_1220_);
lean_ctor_set(v___x_1239_, 1, v___x_1236_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
lean_ctor_set(v___x_1239_, 3, v___y_1214_);
v___x_1240_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1240_, 0, v___y_1220_);
lean_ctor_set(v___x_1240_, 1, v___y_1212_);
lean_ctor_set(v___x_1240_, 2, v___y_1209_);
lean_inc_ref_n(v___x_1240_, 7);
lean_inc(v___x_1235_);
v___x_1241_ = l_Lean_Syntax_node2(v___y_1220_, v___x_1235_, v___x_1239_, v___x_1240_);
lean_inc(v___x_1232_);
v___x_1242_ = l_Lean_Syntax_node2(v___y_1220_, v___x_1232_, v___y_1210_, v___x_1241_);
v___x_1243_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___y_1220_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_inc(v___y_1223_);
v___x_1245_ = l_Lean_Syntax_node1(v___y_1220_, v___y_1223_, v___x_1240_);
v___x_1246_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_1247_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_1248_ = l_Lean_addMacroScope(v___y_1215_, v___x_1247_, v___y_1208_);
v___x_1249_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1249_, 0, v___y_1220_);
lean_ctor_set(v___x_1249_, 1, v___x_1246_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
lean_ctor_set(v___x_1249_, 3, v___y_1214_);
v___x_1250_ = l_Lean_Syntax_node2(v___y_1220_, v___x_1235_, v___x_1249_, v___x_1240_);
v___x_1251_ = l_Lean_Syntax_node2(v___y_1220_, v___x_1232_, v___x_1245_, v___x_1250_);
v___x_1252_ = l_Lean_Syntax_node3(v___y_1220_, v___y_1212_, v___x_1242_, v___x_1244_, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___y_1220_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_Syntax_node3(v___y_1220_, v___x_1228_, v___x_1230_, v___x_1252_, v___x_1254_);
v___x_1256_ = l_Lean_Syntax_node1(v___y_1220_, v___y_1212_, v___x_1255_);
v___x_1257_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_1217_, 3);
v___x_1258_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___y_1217_, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1259_, 0, v___y_1220_);
lean_ctor_set(v___x_1259_, 1, v___x_1257_);
v___x_1260_ = l_Lean_Syntax_node1(v___y_1220_, v___x_1258_, v___x_1259_);
v___x_1261_ = l_Lean_Syntax_node1(v___y_1220_, v___y_1212_, v___x_1260_);
v___x_1262_ = l_Lean_Syntax_node7(v___y_1220_, v___y_1207_, v___x_1226_, v___x_1256_, v___x_1261_, v___x_1240_, v___x_1240_, v___x_1240_, v___x_1240_);
v___x_1263_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1264_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___y_1217_, v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1220_);
lean_ctor_set(v___x_1266_, 1, v___x_1265_);
v___x_1267_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1268_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1213_, v___y_1217_, v___x_1267_);
if (lean_obj_tag(v___y_1218_) == 0)
{
v___y_1139_ = v___y_1204_;
v___y_1140_ = v___y_1206_;
v___y_1141_ = v___y_1209_;
v___y_1142_ = v___x_1262_;
v___y_1143_ = v___y_1211_;
v___y_1144_ = v___y_1212_;
v___y_1145_ = v___y_1213_;
v___y_1146_ = v___x_1266_;
v___y_1147_ = v___y_1216_;
v___y_1148_ = v___x_1264_;
v___y_1149_ = v___y_1217_;
v___y_1150_ = v___x_1268_;
v___y_1151_ = v___y_1219_;
v___y_1152_ = v___y_1220_;
v___y_1153_ = v___y_1221_;
v___y_1154_ = v___y_1222_;
v___y_1155_ = v___x_1240_;
v___y_1156_ = v___y_1205_;
goto v___jp_1138_;
}
else
{
lean_object* v_val_1269_; 
lean_dec(v___y_1205_);
v_val_1269_ = lean_ctor_get(v___y_1218_, 0);
lean_inc(v_val_1269_);
lean_dec_ref(v___y_1218_);
v___y_1139_ = v___y_1204_;
v___y_1140_ = v___y_1206_;
v___y_1141_ = v___y_1209_;
v___y_1142_ = v___x_1262_;
v___y_1143_ = v___y_1211_;
v___y_1144_ = v___y_1212_;
v___y_1145_ = v___y_1213_;
v___y_1146_ = v___x_1266_;
v___y_1147_ = v___y_1216_;
v___y_1148_ = v___x_1264_;
v___y_1149_ = v___y_1217_;
v___y_1150_ = v___x_1268_;
v___y_1151_ = v___y_1219_;
v___y_1152_ = v___y_1220_;
v___y_1153_ = v___y_1221_;
v___y_1154_ = v___y_1222_;
v___y_1155_ = v___x_1240_;
v___y_1156_ = v_val_1269_;
goto v___jp_1138_;
}
}
v___jp_1270_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; size_t v_sz_1299_; lean_object* v___x_1300_; size_t v_sz_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1289_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1290_ = lean_box(2);
lean_inc_n(v___y_1280_, 4);
v___x_1291_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v___y_1280_);
lean_ctor_set(v___x_1291_, 2, v___x_1289_);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___y_1278_);
v___x_1293_ = lean_array_push(v___x_1292_, v___y_1288_);
v___x_1294_ = lean_array_push(v___x_1293_, v___x_1291_);
v___x_1295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1290_);
lean_ctor_set(v___x_1295_, 1, v___y_1271_);
lean_ctor_set(v___x_1295_, 2, v___x_1294_);
v___x_1296_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1281_);
lean_inc_ref_n(v___y_1279_, 6);
v___x_1297_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___y_1281_, v___x_1296_);
v___x_1298_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1299_ = lean_array_size(v___y_1285_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1299_, v___y_1273_, v___y_1285_);
v_sz_1301_ = lean_array_size(v___x_1300_);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1301_, v___y_1273_, v___x_1300_);
lean_inc_ref(v___y_1287_);
v___x_1303_ = l_Array_append___redArg(v___y_1287_, v___x_1302_);
lean_dec_ref(v___x_1302_);
lean_inc_n(v___y_1276_, 14);
v___x_1304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___y_1276_);
lean_ctor_set(v___x_1304_, 1, v___y_1280_);
lean_ctor_set(v___x_1304_, 2, v___x_1303_);
v___x_1305_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1284_, 2);
v___x_1306_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___y_1284_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___y_1276_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1310_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___y_1284_, v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___y_1276_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1314_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___x_1313_, v___x_1298_);
v___x_1315_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___y_1276_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_Syntax_node1(v___y_1276_, v___x_1314_, v___x_1316_);
v___x_1318_ = l_Lean_Syntax_node1(v___y_1276_, v___y_1280_, v___x_1317_);
v___x_1319_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1310_, v___x_1312_, v___x_1318_);
v___x_1320_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1306_, v___x_1308_, v___x_1319_);
v___x_1321_ = l_Lean_Syntax_node1(v___y_1276_, v___y_1280_, v___x_1320_);
v___x_1322_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1297_, v___x_1304_, v___x_1321_);
v___x_1323_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1324_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___y_1281_, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1326_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___y_1276_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1328_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1329_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1279_, v___x_1327_, v___x_1328_);
lean_inc_n(v___y_1283_, 3);
v___x_1330_ = l_Lean_Syntax_node2(v___y_1276_, v___x_1329_, v___y_1283_, v___y_1283_);
v___x_1331_ = l_Lean_Syntax_node4(v___y_1276_, v___x_1324_, v___x_1326_, v___y_1275_, v___x_1330_, v___y_1283_);
v___x_1332_ = l_Lean_Syntax_node5(v___y_1276_, v___y_1274_, v___y_1286_, v___x_1295_, v___x_1322_, v___x_1331_, v___y_1283_);
v___x_1333_ = l_Lean_Syntax_node2(v___y_1276_, v___y_1277_, v___y_1272_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v___y_1282_);
return v___x_1334_;
}
v___jp_1335_:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_inc_ref_n(v___y_1354_, 2);
v___x_1356_ = l_Array_append___redArg(v___y_1354_, v___y_1355_);
lean_dec_ref(v___y_1355_);
lean_inc_n(v___y_1347_, 5);
lean_inc_n(v___y_1339_, 15);
v___x_1357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1357_, 0, v___y_1339_);
lean_ctor_set(v___x_1357_, 1, v___y_1347_);
lean_ctor_set(v___x_1357_, 2, v___x_1356_);
v___x_1358_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1351_, 2);
lean_inc_ref_n(v___y_1344_, 6);
v___x_1359_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___y_1351_, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___y_1339_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
v___x_1362_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1363_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___y_1351_, v___x_1362_);
v___x_1364_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1365_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1366_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___x_1364_, v___x_1365_);
v___x_1367_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1368_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
v___x_1369_ = l_Lean_addMacroScope(v___y_1346_, v___x_1368_, v___y_1340_);
lean_inc(v___y_1345_);
v___x_1370_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1370_, 0, v___y_1339_);
lean_ctor_set(v___x_1370_, 1, v___x_1367_);
lean_ctor_set(v___x_1370_, 2, v___x_1369_);
lean_ctor_set(v___x_1370_, 3, v___y_1345_);
v___x_1371_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1371_, 0, v___y_1339_);
lean_ctor_set(v___x_1371_, 1, v___y_1347_);
lean_ctor_set(v___x_1371_, 2, v___y_1354_);
lean_inc_ref_n(v___x_1371_, 5);
v___x_1372_ = l_Lean_Syntax_node2(v___y_1339_, v___x_1366_, v___x_1370_, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node2(v___y_1339_, v___x_1363_, v___y_1341_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node1(v___y_1339_, v___y_1347_, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1376_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1376_, 0, v___y_1339_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_node3(v___y_1339_, v___x_1359_, v___x_1361_, v___x_1374_, v___x_1376_);
v___x_1378_ = l_Lean_Syntax_node1(v___y_1339_, v___y_1347_, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26));
lean_inc_ref_n(v___y_1348_, 3);
v___x_1380_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___y_1348_, v___x_1379_);
v___x_1381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___y_1339_);
lean_ctor_set(v___x_1381_, 1, v___x_1379_);
v___x_1382_ = l_Lean_Syntax_node1(v___y_1339_, v___x_1380_, v___x_1381_);
v___x_1383_ = l_Lean_Syntax_node1(v___y_1339_, v___y_1347_, v___x_1382_);
v___x_1384_ = l_Lean_Syntax_node7(v___y_1339_, v___y_1352_, v___x_1357_, v___x_1378_, v___x_1383_, v___x_1371_, v___x_1371_, v___x_1371_, v___x_1371_);
v___x_1385_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1386_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___y_1348_, v___x_1385_);
v___x_1387_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___y_1339_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
v___x_1389_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1390_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1344_, v___y_1348_, v___x_1389_);
if (lean_obj_tag(v___y_1350_) == 0)
{
v___y_1271_ = v___x_1390_;
v___y_1272_ = v___x_1384_;
v___y_1273_ = v___y_1336_;
v___y_1274_ = v___x_1386_;
v___y_1275_ = v___y_1338_;
v___y_1276_ = v___y_1339_;
v___y_1277_ = v___y_1343_;
v___y_1278_ = v___y_1342_;
v___y_1279_ = v___y_1344_;
v___y_1280_ = v___y_1347_;
v___y_1281_ = v___y_1348_;
v___y_1282_ = v___y_1349_;
v___y_1283_ = v___x_1371_;
v___y_1284_ = v___y_1351_;
v___y_1285_ = v___y_1353_;
v___y_1286_ = v___x_1388_;
v___y_1287_ = v___y_1354_;
v___y_1288_ = v___y_1337_;
goto v___jp_1270_;
}
else
{
lean_object* v_val_1391_; 
lean_dec(v___y_1337_);
v_val_1391_ = lean_ctor_get(v___y_1350_, 0);
lean_inc(v_val_1391_);
lean_dec_ref(v___y_1350_);
v___y_1271_ = v___x_1390_;
v___y_1272_ = v___x_1384_;
v___y_1273_ = v___y_1336_;
v___y_1274_ = v___x_1386_;
v___y_1275_ = v___y_1338_;
v___y_1276_ = v___y_1339_;
v___y_1277_ = v___y_1343_;
v___y_1278_ = v___y_1342_;
v___y_1279_ = v___y_1344_;
v___y_1280_ = v___y_1347_;
v___y_1281_ = v___y_1348_;
v___y_1282_ = v___y_1349_;
v___y_1283_ = v___x_1371_;
v___y_1284_ = v___y_1351_;
v___y_1285_ = v___y_1353_;
v___y_1286_ = v___x_1388_;
v___y_1287_ = v___y_1354_;
v___y_1288_ = v_val_1391_;
goto v___jp_1270_;
}
}
v___jp_1392_:
{
lean_object* v_quotContext_1410_; lean_object* v_currMacroScope_1411_; lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1506_; 
v_quotContext_1410_ = lean_ctor_get(v___y_1401_, 1);
v_currMacroScope_1411_ = lean_ctor_get(v___y_1401_, 2);
v_ref_1412_ = lean_ctor_get(v___y_1401_, 5);
v___x_1413_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v___y_1394_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_a_1415_ = lean_ctor_get(v___x_1413_, 1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1417_ = v___x_1413_;
v_isShared_1418_ = v_isSharedCheck_1506_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1506_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_1420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v_a_1414_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 2);
lean_ctor_set(v___x_1417_, 1, v___x_1420_);
v___x_1422_ = v___x_1417_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1414_);
lean_ctor_set(v_reuseFailAlloc_1505_, 1, v___x_1420_);
v___x_1422_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; size_t v_sz_1426_; lean_object* v___x_1427_; 
v___x_1423_ = l_Lean_Syntax_node3(v_a_1414_, v___x_1419_, v___y_1406_, v___x_1422_, v___y_1405_);
v___x_1424_ = l_Array_zip___redArg(v___y_1395_, v___y_1403_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v___y_1395_);
v___x_1425_ = l_Array_reverse___redArg(v___x_1424_);
v_sz_1426_ = lean_array_size(v___x_1425_);
v___x_1427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v___x_1425_, v_sz_1426_, v___y_1393_, v___x_1423_, v___y_1401_, v_a_1415_);
lean_dec_ref(v___x_1425_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; lean_object* v_a_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
v_a_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1427_);
v___x_1430_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v_a_1429_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
v_a_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_a_1432_);
lean_dec_ref(v___x_1430_);
v___x_1433_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28);
v___x_1434_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29));
lean_inc(v_currMacroScope_1411_);
lean_inc(v_quotContext_1410_);
v___x_1435_ = l_Lean_addMacroScope(v_quotContext_1410_, v___x_1434_, v_currMacroScope_1411_);
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1437_, 0, v_a_1431_);
lean_ctor_set(v___x_1437_, 1, v___x_1433_);
lean_ctor_set(v___x_1437_, 2, v___x_1435_);
lean_ctor_set(v___x_1437_, 3, v___x_1436_);
if (v___y_1396_ == 0)
{
lean_object* v___x_1438_; lean_object* v_a_1439_; lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1438_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v_a_1432_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
v_a_1440_ = lean_ctor_get(v___x_1438_, 1);
lean_inc(v_a_1440_);
lean_dec_ref(v___x_1438_);
v___x_1441_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1442_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1400_, 2);
v___x_1443_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1441_, v___x_1442_);
v___x_1444_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1445_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1441_, v___x_1444_);
v___x_1446_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1447_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1402_) == 1)
{
lean_object* v_val_1448_; lean_object* v___x_1449_; 
v_val_1448_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_val_1448_);
lean_dec_ref(v___y_1402_);
v___x_1449_ = l_Array_mkArray1___redArg(v_val_1448_);
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_940_ = v___x_1447_;
v___y_941_ = v___y_1393_;
v___y_942_ = v___x_1437_;
v___y_943_ = v_a_1428_;
v___y_944_ = v_currMacroScope_1411_;
v___y_945_ = v___x_1445_;
v___y_946_ = v_a_1440_;
v___y_947_ = v___y_1397_;
v___y_948_ = v___y_1399_;
v___y_949_ = v___y_1400_;
v___y_950_ = v___x_1436_;
v___y_951_ = v_quotContext_1410_;
v___y_952_ = v___x_1446_;
v___y_953_ = v___y_1409_;
v___y_954_ = v_a_1439_;
v___y_955_ = v___y_1404_;
v___y_956_ = v___y_1407_;
v___y_957_ = v___y_1408_;
v___y_958_ = v___x_1443_;
v___y_959_ = v___x_1441_;
v___y_960_ = v___x_1449_;
goto v___jp_939_;
}
else
{
lean_object* v___x_1450_; 
lean_dec(v___y_1402_);
v___x_1450_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_940_ = v___x_1447_;
v___y_941_ = v___y_1393_;
v___y_942_ = v___x_1437_;
v___y_943_ = v_a_1428_;
v___y_944_ = v_currMacroScope_1411_;
v___y_945_ = v___x_1445_;
v___y_946_ = v_a_1440_;
v___y_947_ = v___y_1397_;
v___y_948_ = v___y_1399_;
v___y_949_ = v___y_1400_;
v___y_950_ = v___x_1436_;
v___y_951_ = v_quotContext_1410_;
v___y_952_ = v___x_1446_;
v___y_953_ = v___y_1409_;
v___y_954_ = v_a_1439_;
v___y_955_ = v___y_1404_;
v___y_956_ = v___y_1407_;
v___y_957_ = v___y_1408_;
v___y_958_ = v___x_1443_;
v___y_959_ = v___x_1441_;
v___y_960_ = v___x_1450_;
goto v___jp_939_;
}
}
else
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = l_Lean_Syntax_getArg(v___y_1397_, v___x_873_);
lean_inc(v___x_1451_);
v___x_1452_ = l_Lean_Syntax_matchesNull(v___x_1451_, v___y_1398_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v_a_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1451_);
v___x_1453_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v_a_1432_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
v_a_1455_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1453_);
v___x_1456_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1457_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1400_, 2);
v___x_1458_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1456_, v___x_1457_);
v___x_1459_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1460_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1456_, v___x_1459_);
v___x_1461_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1462_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1402_) == 1)
{
lean_object* v_val_1463_; lean_object* v___x_1464_; 
v_val_1463_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_val_1463_);
lean_dec_ref(v___y_1402_);
v___x_1464_ = l_Array_mkArray1___redArg(v_val_1463_);
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1072_ = v___y_1393_;
v___y_1073_ = v___x_1437_;
v___y_1074_ = v_a_1428_;
v___y_1075_ = v_a_1455_;
v___y_1076_ = v_currMacroScope_1411_;
v___y_1077_ = v___y_1397_;
v___y_1078_ = v___x_1462_;
v___y_1079_ = v___y_1399_;
v___y_1080_ = v___x_1461_;
v___y_1081_ = v___y_1400_;
v___y_1082_ = v___x_1436_;
v___y_1083_ = v___x_1460_;
v___y_1084_ = v_quotContext_1410_;
v___y_1085_ = v___x_1458_;
v___y_1086_ = v___y_1409_;
v___y_1087_ = v_a_1454_;
v___y_1088_ = v___y_1404_;
v___y_1089_ = v___y_1407_;
v___y_1090_ = v___y_1408_;
v___y_1091_ = v___x_1456_;
v___y_1092_ = v___x_1464_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v___y_1402_);
v___x_1465_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1072_ = v___y_1393_;
v___y_1073_ = v___x_1437_;
v___y_1074_ = v_a_1428_;
v___y_1075_ = v_a_1455_;
v___y_1076_ = v_currMacroScope_1411_;
v___y_1077_ = v___y_1397_;
v___y_1078_ = v___x_1462_;
v___y_1079_ = v___y_1399_;
v___y_1080_ = v___x_1461_;
v___y_1081_ = v___y_1400_;
v___y_1082_ = v___x_1436_;
v___y_1083_ = v___x_1460_;
v___y_1084_ = v_quotContext_1410_;
v___y_1085_ = v___x_1458_;
v___y_1086_ = v___y_1409_;
v___y_1087_ = v_a_1454_;
v___y_1088_ = v___y_1404_;
v___y_1089_ = v___y_1407_;
v___y_1090_ = v___y_1408_;
v___y_1091_ = v___x_1456_;
v___y_1092_ = v___x_1465_;
goto v___jp_1071_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1466_ = l_Lean_Syntax_getArg(v___x_1451_, v___x_873_);
lean_dec(v___x_1451_);
v___x_1467_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34));
lean_inc_ref(v___y_1404_);
lean_inc_ref(v___y_1400_);
v___x_1468_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___y_1404_, v___x_1467_);
v___x_1469_ = l_Lean_Syntax_isOfKind(v___x_1466_, v___x_1468_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v_a_1471_; lean_object* v_a_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1470_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v_a_1432_);
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
v_a_1472_ = lean_ctor_get(v___x_1470_, 1);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1470_);
v___x_1473_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1474_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1400_, 2);
v___x_1475_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1473_, v___x_1474_);
v___x_1476_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1477_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1473_, v___x_1476_);
v___x_1478_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1479_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1402_) == 1)
{
lean_object* v_val_1480_; lean_object* v___x_1481_; 
v_val_1480_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_val_1480_);
lean_dec_ref(v___y_1402_);
v___x_1481_ = l_Array_mkArray1___redArg(v_val_1480_);
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1204_ = v___y_1393_;
v___y_1205_ = v___x_1437_;
v___y_1206_ = v_a_1428_;
v___y_1207_ = v___x_1477_;
v___y_1208_ = v_currMacroScope_1411_;
v___y_1209_ = v___x_1479_;
v___y_1210_ = v___y_1397_;
v___y_1211_ = v___y_1399_;
v___y_1212_ = v___x_1478_;
v___y_1213_ = v___y_1400_;
v___y_1214_ = v___x_1436_;
v___y_1215_ = v_quotContext_1410_;
v___y_1216_ = v_a_1472_;
v___y_1217_ = v___x_1473_;
v___y_1218_ = v___y_1409_;
v___y_1219_ = v___x_1475_;
v___y_1220_ = v_a_1471_;
v___y_1221_ = v___y_1404_;
v___y_1222_ = v___y_1407_;
v___y_1223_ = v___y_1408_;
v___y_1224_ = v___x_1481_;
goto v___jp_1203_;
}
else
{
lean_object* v___x_1482_; 
lean_dec(v___y_1402_);
v___x_1482_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1204_ = v___y_1393_;
v___y_1205_ = v___x_1437_;
v___y_1206_ = v_a_1428_;
v___y_1207_ = v___x_1477_;
v___y_1208_ = v_currMacroScope_1411_;
v___y_1209_ = v___x_1479_;
v___y_1210_ = v___y_1397_;
v___y_1211_ = v___y_1399_;
v___y_1212_ = v___x_1478_;
v___y_1213_ = v___y_1400_;
v___y_1214_ = v___x_1436_;
v___y_1215_ = v_quotContext_1410_;
v___y_1216_ = v_a_1472_;
v___y_1217_ = v___x_1473_;
v___y_1218_ = v___y_1409_;
v___y_1219_ = v___x_1475_;
v___y_1220_ = v_a_1471_;
v___y_1221_ = v___y_1404_;
v___y_1222_ = v___y_1407_;
v___y_1223_ = v___y_1408_;
v___y_1224_ = v___x_1482_;
goto v___jp_1203_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v_a_1484_; lean_object* v_a_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1483_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1412_, v___y_1401_, v_a_1432_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
v_a_1485_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_a_1485_);
lean_dec_ref(v___x_1483_);
v___x_1486_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1487_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1400_, 2);
v___x_1488_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1486_, v___x_1487_);
v___x_1489_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1490_ = l_Lean_Name_mkStr4(v___x_868_, v___y_1400_, v___x_1486_, v___x_1489_);
v___x_1491_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1492_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1402_) == 1)
{
lean_object* v_val_1493_; lean_object* v___x_1494_; 
v_val_1493_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_val_1493_);
lean_dec_ref(v___y_1402_);
v___x_1494_ = l_Array_mkArray1___redArg(v_val_1493_);
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1336_ = v___y_1393_;
v___y_1337_ = v___x_1437_;
v___y_1338_ = v_a_1428_;
v___y_1339_ = v_a_1484_;
v___y_1340_ = v_currMacroScope_1411_;
v___y_1341_ = v___y_1397_;
v___y_1342_ = v___y_1399_;
v___y_1343_ = v___x_1488_;
v___y_1344_ = v___y_1400_;
v___y_1345_ = v___x_1436_;
v___y_1346_ = v_quotContext_1410_;
v___y_1347_ = v___x_1491_;
v___y_1348_ = v___x_1486_;
v___y_1349_ = v_a_1485_;
v___y_1350_ = v___y_1409_;
v___y_1351_ = v___y_1404_;
v___y_1352_ = v___x_1490_;
v___y_1353_ = v___y_1407_;
v___y_1354_ = v___x_1492_;
v___y_1355_ = v___x_1494_;
goto v___jp_1335_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v___y_1402_);
v___x_1495_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1410_);
lean_inc(v_currMacroScope_1411_);
v___y_1336_ = v___y_1393_;
v___y_1337_ = v___x_1437_;
v___y_1338_ = v_a_1428_;
v___y_1339_ = v_a_1484_;
v___y_1340_ = v_currMacroScope_1411_;
v___y_1341_ = v___y_1397_;
v___y_1342_ = v___y_1399_;
v___y_1343_ = v___x_1488_;
v___y_1344_ = v___y_1400_;
v___y_1345_ = v___x_1436_;
v___y_1346_ = v_quotContext_1410_;
v___y_1347_ = v___x_1491_;
v___y_1348_ = v___x_1486_;
v___y_1349_ = v_a_1485_;
v___y_1350_ = v___y_1409_;
v___y_1351_ = v___y_1404_;
v___y_1352_ = v___x_1490_;
v___y_1353_ = v___y_1407_;
v___y_1354_ = v___x_1492_;
v___y_1355_ = v___x_1495_;
goto v___jp_1335_;
}
}
}
}
}
else
{
lean_object* v_a_1496_; lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1402_);
lean_dec(v___y_1397_);
v_a_1496_ = lean_ctor_get(v___x_1427_, 0);
v_a_1497_ = lean_ctor_get(v___x_1427_, 1);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1427_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_inc(v_a_1496_);
lean_dec(v___x_1427_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1496_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
v___jp_1507_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = l_Lean_Syntax_getArg(v_x_865_, v___x_1511_);
v___x_1513_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_1514_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v___x_1515_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35));
lean_inc(v___x_1512_);
v___x_1516_ = l_Lean_Syntax_isOfKind(v___x_1512_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
lean_dec(v___x_1512_);
lean_dec(v_doc_x3f_1508_);
lean_dec(v_x_865_);
v___x_1517_ = lean_box(1);
v___x_1518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___y_1510_);
return v___x_1518_;
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1519_ = lean_unsigned_to_nat(6u);
v___x_1520_ = l_Lean_Syntax_getArg(v_x_865_, v___x_1519_);
v___x_1521_ = l_Lean_Syntax_getArgs(v___x_1520_);
lean_dec(v___x_1520_);
v_sz_1522_ = lean_array_size(v___x_1521_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_1522_, v___x_1523_, v___x_1521_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
lean_dec(v___x_1512_);
lean_dec(v_doc_x3f_1508_);
lean_dec(v_x_865_);
v___x_1525_ = lean_box(1);
v___x_1526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___y_1510_);
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_val_1527_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v___x_1524_);
v___x_1528_ = lean_unsigned_to_nat(8u);
v___x_1529_ = l_Lean_Syntax_getArg(v_x_865_, v___x_1528_);
v___x_1530_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_1529_);
v___x_1531_ = l_Lean_Syntax_isOfKind(v___x_1529_, v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v___x_1529_);
lean_dec(v_val_1527_);
lean_dec(v___x_1512_);
lean_dec(v_doc_x3f_1508_);
lean_dec(v_x_865_);
v___x_1532_ = lean_box(1);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___y_1510_);
return v___x_1533_;
}
else
{
size_t v_sz_1534_; lean_object* v___x_1535_; lean_object* v_cs_u2082_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_cs_u2081_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_bs_1544_; lean_object* v___x_1545_; 
v_sz_1534_ = lean_array_size(v_val_1527_);
v___x_1535_ = lean_unsigned_to_nat(2u);
lean_inc(v_val_1527_);
v_cs_u2082_1536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_1534_, v___x_1523_, v_val_1527_);
v___x_1537_ = lean_unsigned_to_nat(3u);
v___x_1538_ = l_Lean_Syntax_getArg(v_x_865_, v___x_1537_);
v___x_1539_ = lean_unsigned_to_nat(4u);
v___x_1540_ = l_Lean_Syntax_getArg(v_x_865_, v___x_1539_);
lean_dec(v_x_865_);
v_cs_u2081_1541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_1534_, v___x_1523_, v_val_1527_);
v___x_1542_ = l_Lean_Syntax_getArg(v___x_1529_, v___x_873_);
v___x_1543_ = l_Lean_Syntax_getArg(v___x_1529_, v___x_1535_);
lean_dec(v___x_1529_);
v_bs_1544_ = l_Lean_Syntax_getArgs(v___x_1540_);
lean_dec(v___x_1540_);
v___x_1545_ = l_Lean_Syntax_getOptional_x3f(v___x_1538_);
lean_dec(v___x_1538_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_box(0);
v___y_1393_ = v___x_1523_;
v___y_1394_ = v___y_1510_;
v___y_1395_ = v_cs_u2081_1541_;
v___y_1396_ = v___x_1516_;
v___y_1397_ = v___x_1512_;
v___y_1398_ = v___x_1511_;
v___y_1399_ = v___x_1535_;
v___y_1400_ = v___x_1513_;
v___y_1401_ = v___y_1509_;
v___y_1402_ = v_doc_x3f_1508_;
v___y_1403_ = v_cs_u2082_1536_;
v___y_1404_ = v___x_1514_;
v___y_1405_ = v___x_1543_;
v___y_1406_ = v___x_1542_;
v___y_1407_ = v_bs_1544_;
v___y_1408_ = v___x_1515_;
v___y_1409_ = v___x_1546_;
goto v___jp_1392_;
}
else
{
lean_object* v_val_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_val_1547_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1545_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_val_1547_);
lean_dec(v___x_1545_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_val_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
v___y_1393_ = v___x_1523_;
v___y_1394_ = v___y_1510_;
v___y_1395_ = v_cs_u2081_1541_;
v___y_1396_ = v___x_1516_;
v___y_1397_ = v___x_1512_;
v___y_1398_ = v___x_1511_;
v___y_1399_ = v___x_1535_;
v___y_1400_ = v___x_1513_;
v___y_1401_ = v___y_1509_;
v___y_1402_ = v_doc_x3f_1508_;
v___y_1403_ = v_cs_u2082_1536_;
v___y_1404_ = v___x_1514_;
v___y_1405_ = v___x_1543_;
v___y_1406_ = v___x_1542_;
v___y_1407_ = v_bs_1544_;
v___y_1408_ = v___x_1515_;
v___y_1409_ = v___x_1552_;
goto v___jp_1392_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___boxed(lean_object* v_x_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(v_x_1568_, v_a_1569_, v_a_1570_);
lean_dec_ref(v_a_1569_);
return v_res_1571_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1578_ = l_Lean_explicitBinders;
v___x_1579_ = ((lean_object*)(l_term_u2203___x2c___00__closed__3));
v___x_1580_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1581_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___x_1579_);
lean_ctor_set(v___x_1581_, 2, v___x_1578_);
return v___x_1581_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1582_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1583_ = lean_obj_once(&l_term_u2203___x2c___00__closed__4, &l_term_u2203___x2c___00__closed__4_once, _init_l_term_u2203___x2c___00__closed__4);
v___x_1584_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1585_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
lean_ctor_set(v___x_1585_, 2, v___x_1582_);
return v___x_1585_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1587_ = lean_obj_once(&l_term_u2203___x2c___00__closed__5, &l_term_u2203___x2c___00__closed__5_once, _init_l_term_u2203___x2c___00__closed__5);
v___x_1588_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1589_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
lean_ctor_set(v___x_1589_, 2, v___x_1586_);
return v___x_1589_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = lean_obj_once(&l_term_u2203___x2c___00__closed__6, &l_term_u2203___x2c___00__closed__6_once, _init_l_term_u2203___x2c___00__closed__6);
v___x_1591_ = lean_unsigned_to_nat(1022u);
v___x_1592_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_1593_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1591_);
lean_ctor_set(v___x_1593_, 2, v___x_1590_);
return v___x_1593_;
}
}
static lean_object* _init_l_term_u2203___x2c__(void){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_obj_once(&l_term_u2203___x2c___00__closed__7, &l_term_u2203___x2c___00__closed__7_once, _init_l_term_u2203___x2c___00__closed__7);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(lean_object* v_x_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1601_; uint8_t v___x_1602_; 
v___x_1601_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v_x_1598_);
v___x_1602_ = l_Lean_Syntax_isOfKind(v_x_1598_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; 
lean_dec(v_x_1598_);
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_a_1600_);
return v___x_1604_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1605_);
v___x_1607_ = lean_unsigned_to_nat(3u);
v___x_1608_ = l_Lean_Syntax_getArg(v_x_1598_, v___x_1607_);
lean_dec(v_x_1598_);
v___x_1609_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1610_ = l_Lean_expandExplicitBinders(v___x_1609_, v___x_1606_, v___x_1608_, v_a_1599_, v_a_1600_);
lean_dec(v___x_1606_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___boxed(lean_object* v_x_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(v_x_1611_, v_a_1612_, v_a_1613_);
lean_dec_ref(v_a_1612_);
return v_res_1614_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1621_ = l_Lean_explicitBinders;
v___x_1622_ = ((lean_object*)(l_termExists___x2c___00__closed__3));
v___x_1623_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1624_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v___x_1622_);
lean_ctor_set(v___x_1624_, 2, v___x_1621_);
return v___x_1624_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1625_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1626_ = lean_obj_once(&l_termExists___x2c___00__closed__4, &l_termExists___x2c___00__closed__4_once, _init_l_termExists___x2c___00__closed__4);
v___x_1627_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1628_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
lean_ctor_set(v___x_1628_, 1, v___x_1626_);
lean_ctor_set(v___x_1628_, 2, v___x_1625_);
return v___x_1628_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1629_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1630_ = lean_obj_once(&l_termExists___x2c___00__closed__5, &l_termExists___x2c___00__closed__5_once, _init_l_termExists___x2c___00__closed__5);
v___x_1631_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1632_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v___x_1629_);
return v___x_1632_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1633_ = lean_obj_once(&l_termExists___x2c___00__closed__6, &l_termExists___x2c___00__closed__6_once, _init_l_termExists___x2c___00__closed__6);
v___x_1634_ = lean_unsigned_to_nat(1022u);
v___x_1635_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
v___x_1636_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1634_);
lean_ctor_set(v___x_1636_, 2, v___x_1633_);
return v___x_1636_;
}
}
static lean_object* _init_l_termExists___x2c__(void){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_obj_once(&l_termExists___x2c___00__closed__7, &l_termExists___x2c___00__closed__7_once, _init_l_termExists___x2c___00__closed__7);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(lean_object* v_x_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
lean_inc(v_x_1638_);
v___x_1642_ = l_Lean_Syntax_isOfKind(v_x_1638_, v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_x_1638_);
v___x_1643_ = lean_box(1);
v___x_1644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v_a_1640_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1645_ = lean_unsigned_to_nat(1u);
v___x_1646_ = l_Lean_Syntax_getArg(v_x_1638_, v___x_1645_);
v___x_1647_ = lean_unsigned_to_nat(3u);
v___x_1648_ = l_Lean_Syntax_getArg(v_x_1638_, v___x_1647_);
lean_dec(v_x_1638_);
v___x_1649_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1650_ = l_Lean_expandExplicitBinders(v___x_1649_, v___x_1646_, v___x_1648_, v_a_1639_, v_a_1640_);
lean_dec(v___x_1646_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1___boxed(lean_object* v_x_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(v_x_1651_, v_a_1652_, v_a_1653_);
lean_dec_ref(v_a_1652_);
return v_res_1654_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = l_Lean_explicitBinders;
v___x_1662_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__3));
v___x_1663_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1664_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
lean_ctor_set(v___x_1664_, 1, v___x_1662_);
lean_ctor_set(v___x_1664_, 2, v___x_1661_);
return v___x_1664_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1665_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1666_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__4, &l_term_u03a3___x2c___00__closed__4_once, _init_l_term_u03a3___x2c___00__closed__4);
v___x_1667_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1668_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
lean_ctor_set(v___x_1668_, 1, v___x_1666_);
lean_ctor_set(v___x_1668_, 2, v___x_1665_);
return v___x_1668_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1670_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__5, &l_term_u03a3___x2c___00__closed__5_once, _init_l_term_u03a3___x2c___00__closed__5);
v___x_1671_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1672_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1669_);
return v___x_1672_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__6, &l_term_u03a3___x2c___00__closed__6_once, _init_l_term_u03a3___x2c___00__closed__6);
v___x_1674_ = lean_unsigned_to_nat(1022u);
v___x_1675_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
v___x_1676_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
lean_ctor_set(v___x_1676_, 2, v___x_1673_);
return v___x_1676_;
}
}
static lean_object* _init_l_term_u03a3___x2c__(void){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__7, &l_term_u03a3___x2c___00__closed__7_once, _init_l_term_u03a3___x2c___00__closed__7);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(lean_object* v_x_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v___x_1684_; uint8_t v___x_1685_; 
v___x_1684_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
lean_inc(v_x_1681_);
v___x_1685_ = l_Lean_Syntax_isOfKind(v_x_1681_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
lean_dec(v_x_1681_);
v___x_1686_ = lean_box(1);
v___x_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_a_1683_);
return v___x_1687_;
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1688_ = lean_unsigned_to_nat(1u);
v___x_1689_ = l_Lean_Syntax_getArg(v_x_1681_, v___x_1688_);
v___x_1690_ = lean_unsigned_to_nat(3u);
v___x_1691_ = l_Lean_Syntax_getArg(v_x_1681_, v___x_1690_);
lean_dec(v_x_1681_);
v___x_1692_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1693_ = l_Lean_expandExplicitBinders(v___x_1692_, v___x_1689_, v___x_1691_, v_a_1682_, v_a_1683_);
lean_dec(v___x_1689_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___boxed(lean_object* v_x_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(v_x_1694_, v_a_1695_, v_a_1696_);
lean_dec_ref(v_a_1695_);
return v_res_1697_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1704_ = l_Lean_explicitBinders;
v___x_1705_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__3));
v___x_1706_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1707_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v___x_1705_);
lean_ctor_set(v___x_1707_, 2, v___x_1704_);
return v___x_1707_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1708_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1709_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__4, &l_term_u03a3_x27___x2c___00__closed__4_once, _init_l_term_u03a3_x27___x2c___00__closed__4);
v___x_1710_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1711_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1710_);
lean_ctor_set(v___x_1711_, 1, v___x_1709_);
lean_ctor_set(v___x_1711_, 2, v___x_1708_);
return v___x_1711_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1713_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__5, &l_term_u03a3_x27___x2c___00__closed__5_once, _init_l_term_u03a3_x27___x2c___00__closed__5);
v___x_1714_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1715_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___x_1713_);
lean_ctor_set(v___x_1715_, 2, v___x_1712_);
return v___x_1715_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1716_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__6, &l_term_u03a3_x27___x2c___00__closed__6_once, _init_l_term_u03a3_x27___x2c___00__closed__6);
v___x_1717_ = lean_unsigned_to_nat(1022u);
v___x_1718_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
v___x_1719_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
lean_ctor_set(v___x_1719_, 2, v___x_1716_);
return v___x_1719_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c__(void){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__7, &l_term_u03a3_x27___x2c___00__closed__7_once, _init_l_term_u03a3_x27___x2c___00__closed__7);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(lean_object* v_x_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
lean_inc(v_x_1724_);
v___x_1728_ = l_Lean_Syntax_isOfKind(v_x_1724_, v___x_1727_);
if (v___x_1728_ == 0)
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v_x_1724_);
v___x_1729_ = lean_box(1);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
lean_ctor_set(v___x_1730_, 1, v_a_1726_);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v___x_1732_ = l_Lean_Syntax_getArg(v_x_1724_, v___x_1731_);
v___x_1733_ = lean_unsigned_to_nat(3u);
v___x_1734_ = l_Lean_Syntax_getArg(v_x_1724_, v___x_1733_);
lean_dec(v_x_1724_);
v___x_1735_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1736_ = l_Lean_expandExplicitBinders(v___x_1735_, v___x_1732_, v___x_1734_, v_a_1725_, v_a_1726_);
lean_dec(v___x_1732_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___boxed(lean_object* v_x_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(v_x_1737_, v_a_1738_, v_a_1739_);
lean_dec_ref(v_a_1738_);
return v_res_1740_;
}
}
static lean_object* _init_l_term___xd7____1___closed__4(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1747_ = ((lean_object*)(l_term___xd7____1___closed__3));
v___x_1748_ = l_Lean_bracketedExplicitBinders;
v___x_1749_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1750_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1748_);
lean_ctor_set(v___x_1750_, 2, v___x_1747_);
return v___x_1750_;
}
}
static lean_object* _init_l_term___xd7____1___closed__6(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1755_ = lean_obj_once(&l_term___xd7____1___closed__4, &l_term___xd7____1___closed__4_once, _init_l_term___xd7____1___closed__4);
v___x_1756_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1757_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
lean_ctor_set(v___x_1757_, 2, v___x_1754_);
return v___x_1757_;
}
}
static lean_object* _init_l_term___xd7____1___closed__7(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1758_ = lean_obj_once(&l_term___xd7____1___closed__6, &l_term___xd7____1___closed__6_once, _init_l_term___xd7____1___closed__6);
v___x_1759_ = lean_unsigned_to_nat(35u);
v___x_1760_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_1761_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___x_1759_);
lean_ctor_set(v___x_1761_, 2, v___x_1758_);
return v___x_1761_;
}
}
static lean_object* _init_l_term___xd7____1(void){
_start:
{
lean_object* v___x_1762_; 
v___x_1762_ = lean_obj_once(&l_term___xd7____1___closed__7, &l_term___xd7____1___closed__7_once, _init_l_term___xd7____1___closed__7);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(lean_object* v_x_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_){
_start:
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_term___xd7____1___closed__1));
lean_inc(v_x_1763_);
v___x_1767_ = l_Lean_Syntax_isOfKind(v_x_1763_, v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_x_1763_);
v___x_1768_ = lean_box(1);
v___x_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v_a_1765_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = l_Lean_Syntax_getArg(v_x_1763_, v___x_1770_);
v___x_1772_ = lean_unsigned_to_nat(2u);
v___x_1773_ = l_Lean_Syntax_getArg(v_x_1763_, v___x_1772_);
lean_dec(v_x_1763_);
v___x_1774_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1775_ = l_Lean_expandBracketedBinders(v___x_1774_, v___x_1771_, v___x_1773_, v_a_1764_, v_a_1765_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1___boxed(lean_object* v_x_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(v_x_1776_, v_a_1777_, v_a_1778_);
lean_dec_ref(v_a_1777_);
return v_res_1779_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__4(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = ((lean_object*)(l_term___xd7_x27____1___closed__3));
v___x_1787_ = l_Lean_bracketedExplicitBinders;
v___x_1788_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1789_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1789_, 0, v___x_1788_);
lean_ctor_set(v___x_1789_, 1, v___x_1787_);
lean_ctor_set(v___x_1789_, 2, v___x_1786_);
return v___x_1789_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__5(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1790_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1791_ = lean_obj_once(&l_term___xd7_x27____1___closed__4, &l_term___xd7_x27____1___closed__4_once, _init_l_term___xd7_x27____1___closed__4);
v___x_1792_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1793_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1793_, 0, v___x_1792_);
lean_ctor_set(v___x_1793_, 1, v___x_1791_);
lean_ctor_set(v___x_1793_, 2, v___x_1790_);
return v___x_1793_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__6(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = lean_obj_once(&l_term___xd7_x27____1___closed__5, &l_term___xd7_x27____1___closed__5_once, _init_l_term___xd7_x27____1___closed__5);
v___x_1795_ = lean_unsigned_to_nat(35u);
v___x_1796_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_1797_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1795_);
lean_ctor_set(v___x_1797_, 2, v___x_1794_);
return v___x_1797_;
}
}
static lean_object* _init_l_term___xd7_x27____1(void){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_obj_once(&l_term___xd7_x27____1___closed__6, &l_term___xd7_x27____1___closed__6_once, _init_l_term___xd7_x27____1___closed__6);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(lean_object* v_x_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
lean_inc(v_x_1799_);
v___x_1803_ = l_Lean_Syntax_isOfKind(v_x_1799_, v___x_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_x_1799_);
v___x_1804_ = lean_box(1);
v___x_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1801_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1806_);
v___x_1808_ = lean_unsigned_to_nat(2u);
v___x_1809_ = l_Lean_Syntax_getArg(v_x_1799_, v___x_1808_);
lean_dec(v_x_1799_);
v___x_1810_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1811_ = l_Lean_expandBracketedBinders(v___x_1810_, v___x_1807_, v___x_1809_, v_a_1800_, v_a_1801_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1___boxed(lean_object* v_x_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(v_x_1812_, v_a_1813_, v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(lean_object* v_x_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_convCalc___00__closed__1));
lean_inc(v_x_1975_);
v___x_1979_ = l_Lean_Syntax_isOfKind(v_x_1975_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_x_1975_);
v___x_1980_ = lean_box(1);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_a_1977_);
return v___x_1981_;
}
else
{
lean_object* v_ref_1982_; lean_object* v___x_1983_; lean_object* v_tk_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_ref_1982_ = lean_ctor_get(v_a_1976_, 5);
v___x_1983_ = lean_unsigned_to_nat(0u);
v_tk_1984_ = l_Lean_Syntax_getArg(v_x_1975_, v___x_1983_);
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = l_Lean_Syntax_getArg(v_x_1975_, v___x_1985_);
lean_dec(v_x_1975_);
v___x_1987_ = 0;
v___x_1988_ = l_Lean_SourceInfo_fromRef(v_ref_1982_, v___x_1987_);
v___x_1989_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3));
v___x_1990_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4));
lean_inc_n(v___x_1988_, 6);
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1988_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_1995_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_1996_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1997_ = ((lean_object*)(l_Lean_calcTactic___closed__1));
v___x_1998_ = l_Lean_SourceInfo_fromRef(v_tk_1984_, v___x_1979_);
lean_dec(v_tk_1984_);
v___x_1999_ = ((lean_object*)(l_Lean_calc___closed__0));
v___x_2000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1998_);
lean_ctor_set(v___x_2000_, 1, v___x_1999_);
v___x_2001_ = l_Lean_Syntax_node2(v___x_1988_, v___x_1997_, v___x_2000_, v___x_1986_);
v___x_2002_ = l_Lean_Syntax_node1(v___x_1988_, v___x_1996_, v___x_2001_);
v___x_2003_ = l_Lean_Syntax_node1(v___x_1988_, v___x_1995_, v___x_2002_);
v___x_2004_ = l_Lean_Syntax_node1(v___x_1988_, v___x_1994_, v___x_2003_);
v___x_2005_ = l_Lean_Syntax_node3(v___x_1988_, v___x_1989_, v___x_1991_, v___x_1993_, v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_a_1977_);
return v___x_2006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___boxed(lean_object* v_x_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(v_x_2007_, v_a_2008_, v_a_2009_);
lean_dec_ref(v_a_2008_);
return v_res_2010_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__9(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = ((lean_object*)(l_unexpandUnit___redArg___closed__8));
v___x_2031_ = l_String_toRawSubstring_x27(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__10(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_box(0);
v___x_2034_ = ((lean_object*)(l_unexpandUnit___redArg___closed__1));
v___x_2035_ = l_Lean_addMacroScope(v___x_2034_, v___x_2033_, v___x_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg(lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2050_ = 0;
v___x_2051_ = l_Lean_SourceInfo_fromRef(v_a_2048_, v___x_2050_);
v___x_2052_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
v___x_2053_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_2054_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2051_, 6);
v___x_2055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2051_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2057_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2058_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2059_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2051_);
lean_ctor_set(v___x_2060_, 1, v___x_2057_);
lean_ctor_set(v___x_2060_, 2, v___x_2058_);
lean_ctor_set(v___x_2060_, 3, v___x_2059_);
v___x_2061_ = l_Lean_Syntax_node1(v___x_2051_, v___x_2056_, v___x_2060_);
v___x_2062_ = l_Lean_Syntax_node2(v___x_2051_, v___x_2053_, v___x_2055_, v___x_2061_);
v___x_2063_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2064_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2051_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
lean_ctor_set(v___x_2065_, 2, v___x_2064_);
v___x_2066_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2067_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2051_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = l_Lean_Syntax_node3(v___x_2051_, v___x_2052_, v___x_2062_, v___x_2065_, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_a_2049_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg___boxed(lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_unexpandUnit___redArg(v_a_2070_, v_a_2071_);
lean_dec(v_a_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit(lean_object* v_x_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_unexpandUnit___redArg(v_a_2074_, v_a_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___boxed(lean_object* v_x_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_unexpandUnit(v_x_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2078_);
lean_dec(v_x_2077_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg(lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
uint8_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2087_ = 0;
v___x_2088_ = l_Lean_SourceInfo_fromRef(v_a_2085_, v___x_2087_);
v___x_2089_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
v___x_2090_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2088_, 3);
v___x_2091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2088_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2093_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2094_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2088_);
lean_ctor_set(v___x_2094_, 1, v___x_2092_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2088_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = l_Lean_Syntax_node3(v___x_2088_, v___x_2089_, v___x_2091_, v___x_2094_, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
lean_ctor_set(v___x_2098_, 1, v_a_2086_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg___boxed(lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_unexpandListNil___redArg(v_a_2099_, v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil(lean_object* v_x_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_unexpandListNil___redArg(v_a_2103_, v_a_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___boxed(lean_object* v_x_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_unexpandListNil(v_x_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2107_);
lean_dec(v_x_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_unexpandListCons(lean_object* v_x_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2116_);
v___x_2120_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec(v_x_2116_);
v___x_2121_ = lean_box(0);
v___x_2122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
lean_ctor_set(v___x_2122_, 1, v_a_2118_);
return v___x_2122_;
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = l_Lean_Syntax_getArg(v_x_2116_, v___x_2123_);
lean_dec(v_x_2116_);
v___x_2125_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2124_);
v___x_2126_ = l_Lean_Syntax_matchesNull(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_a_2118_);
return v___x_2128_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2129_ = lean_unsigned_to_nat(0u);
v___x_2130_ = l_Lean_Syntax_getArg(v___x_2124_, v___x_2129_);
v___x_2131_ = l_Lean_Syntax_getArg(v___x_2124_, v___x_2123_);
lean_dec(v___x_2124_);
v___x_2132_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2131_);
v___x_2133_ = l_Lean_Syntax_isOfKind(v___x_2131_, v___x_2132_);
if (v___x_2133_ == 0)
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_unexpandListCons___closed__1));
lean_inc(v___x_2131_);
v___x_2135_ = l_Lean_Syntax_isOfKind(v___x_2131_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
lean_dec(v___x_2131_);
lean_dec(v___x_2130_);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
lean_ctor_set(v___x_2137_, 1, v_a_2118_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2138_ = l_Lean_SourceInfo_fromRef(v_a_2117_, v___x_2133_);
v___x_2139_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2138_, 4);
v___x_2140_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2138_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2142_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2143_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2138_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_Syntax_node3(v___x_2138_, v___x_2141_, v___x_2130_, v___x_2143_, v___x_2131_);
v___x_2145_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2138_);
lean_ctor_set(v___x_2146_, 1, v___x_2145_);
v___x_2147_ = l_Lean_Syntax_node3(v___x_2138_, v___x_2132_, v___x_2140_, v___x_2144_, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v_a_2118_);
return v___x_2148_;
}
}
else
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_Syntax_getArg(v___x_2131_, v___x_2123_);
lean_dec(v___x_2131_);
lean_inc(v___x_2149_);
v___x_2150_ = l_Lean_Syntax_matchesNull(v___x_2149_, v___x_2129_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2151_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2152_ = l_Lean_Syntax_getArgs(v___x_2149_);
lean_dec(v___x_2149_);
v___x_2153_ = l_Lean_SourceInfo_fromRef(v_a_2117_, v___x_2150_);
v___x_2154_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2153_, 4);
v___x_2155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2153_);
lean_ctor_set(v___x_2157_, 1, v___x_2151_);
v___x_2158_ = l_Array_mkArray2___redArg(v___x_2130_, v___x_2157_);
v___x_2159_ = l_Array_append___redArg(v___x_2158_, v___x_2152_);
lean_dec_ref(v___x_2152_);
v___x_2160_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2153_);
lean_ctor_set(v___x_2160_, 1, v___x_2156_);
lean_ctor_set(v___x_2160_, 2, v___x_2159_);
v___x_2161_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2153_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_Syntax_node3(v___x_2153_, v___x_2132_, v___x_2155_, v___x_2160_, v___x_2162_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v_a_2118_);
return v___x_2164_;
}
else
{
uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec(v___x_2149_);
v___x_2165_ = 0;
v___x_2166_ = l_Lean_SourceInfo_fromRef(v_a_2117_, v___x_2165_);
v___x_2167_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2166_, 3);
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2170_ = l_Lean_Syntax_node1(v___x_2166_, v___x_2169_, v___x_2130_);
v___x_2171_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2166_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_Syntax_node3(v___x_2166_, v___x_2132_, v___x_2168_, v___x_2170_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_a_2118_);
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListCons___boxed(lean_object* v_x_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_unexpandListCons(v_x_2175_, v_a_2176_, v_a_2177_);
lean_dec(v_a_2176_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray(lean_object* v_x_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2183_);
v___x_2187_ = l_Lean_Syntax_isOfKind(v_x_2183_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v_x_2183_);
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_a_2185_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = lean_unsigned_to_nat(1u);
v___x_2191_ = l_Lean_Syntax_getArg(v_x_2183_, v___x_2190_);
lean_dec(v_x_2183_);
lean_inc(v___x_2191_);
v___x_2192_ = l_Lean_Syntax_matchesNull(v___x_2191_, v___x_2190_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_dec(v___x_2191_);
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v_a_2185_);
return v___x_2194_;
}
else
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2195_ = lean_unsigned_to_nat(0u);
v___x_2196_ = l_Lean_Syntax_getArg(v___x_2191_, v___x_2195_);
lean_dec(v___x_2191_);
v___x_2197_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2196_);
v___x_2198_ = l_Lean_Syntax_isOfKind(v___x_2196_, v___x_2197_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v_a_2185_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2201_ = l_Lean_Syntax_getArg(v___x_2196_, v___x_2190_);
lean_dec(v___x_2196_);
v___x_2202_ = l_Lean_Syntax_getArgs(v___x_2201_);
lean_dec(v___x_2201_);
v___x_2203_ = 0;
v___x_2204_ = l_Lean_SourceInfo_fromRef(v_a_2184_, v___x_2203_);
v___x_2205_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_2206_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_2204_, 3);
v___x_2207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2204_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2209_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2210_ = l_Array_append___redArg(v___x_2209_, v___x_2202_);
lean_dec_ref(v___x_2202_);
v___x_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2204_);
lean_ctor_set(v___x_2211_, 1, v___x_2208_);
lean_ctor_set(v___x_2211_, 2, v___x_2210_);
v___x_2212_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2213_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2204_);
lean_ctor_set(v___x_2213_, 1, v___x_2212_);
v___x_2214_ = l_Lean_Syntax_node3(v___x_2204_, v___x_2205_, v___x_2207_, v___x_2211_, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v_a_2185_);
return v___x_2215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray___boxed(lean_object* v_x_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_unexpandListToArray(v_x_2216_, v_a_2217_, v_a_2218_);
lean_dec(v_a_2217_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk(lean_object* v_x_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2223_; uint8_t v___x_2224_; 
v___x_2223_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2220_);
v___x_2224_ = l_Lean_Syntax_isOfKind(v_x_2220_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_x_2220_);
v___x_2225_ = lean_box(0);
v___x_2226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
lean_ctor_set(v___x_2226_, 1, v_a_2222_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = l_Lean_Syntax_getArg(v_x_2220_, v___x_2227_);
lean_dec(v_x_2220_);
v___x_2229_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2228_);
v___x_2230_ = l_Lean_Syntax_matchesNull(v___x_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; 
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v_a_2222_);
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = l_Lean_Syntax_getArg(v___x_2228_, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_getArg(v___x_2228_, v___x_2227_);
lean_dec(v___x_2228_);
v___x_2236_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
lean_inc(v___x_2235_);
v___x_2237_ = l_Lean_Syntax_isOfKind(v___x_2235_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2238_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2237_);
v___x_2239_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_2240_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2238_, 8);
v___x_2241_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2241_, 0, v___x_2238_);
lean_ctor_set(v___x_2241_, 1, v___x_2240_);
v___x_2242_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2243_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2244_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2245_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2238_);
lean_ctor_set(v___x_2246_, 1, v___x_2243_);
lean_ctor_set(v___x_2246_, 2, v___x_2244_);
lean_ctor_set(v___x_2246_, 3, v___x_2245_);
v___x_2247_ = l_Lean_Syntax_node1(v___x_2238_, v___x_2242_, v___x_2246_);
v___x_2248_ = l_Lean_Syntax_node2(v___x_2238_, v___x_2239_, v___x_2241_, v___x_2247_);
v___x_2249_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2250_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2238_);
lean_ctor_set(v___x_2251_, 1, v___x_2250_);
v___x_2252_ = l_Lean_Syntax_node1(v___x_2238_, v___x_2249_, v___x_2235_);
v___x_2253_ = l_Lean_Syntax_node3(v___x_2238_, v___x_2249_, v___x_2234_, v___x_2251_, v___x_2252_);
v___x_2254_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2238_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node3(v___x_2238_, v___x_2236_, v___x_2248_, v___x_2253_, v___x_2255_);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v_a_2222_);
return v___x_2257_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2258_ = l_Lean_Syntax_getArg(v___x_2235_, v___x_2233_);
v___x_2259_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2258_);
v___x_2260_ = l_Lean_Syntax_isOfKind(v___x_2258_, v___x_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec(v___x_2258_);
v___x_2261_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2260_);
v___x_2262_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2261_, 8);
v___x_2263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2265_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2266_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2267_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2268_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2261_);
lean_ctor_set(v___x_2268_, 1, v___x_2265_);
lean_ctor_set(v___x_2268_, 2, v___x_2266_);
lean_ctor_set(v___x_2268_, 3, v___x_2267_);
v___x_2269_ = l_Lean_Syntax_node1(v___x_2261_, v___x_2264_, v___x_2268_);
v___x_2270_ = l_Lean_Syntax_node2(v___x_2261_, v___x_2259_, v___x_2263_, v___x_2269_);
v___x_2271_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2272_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2261_);
lean_ctor_set(v___x_2273_, 1, v___x_2272_);
v___x_2274_ = l_Lean_Syntax_node1(v___x_2261_, v___x_2271_, v___x_2235_);
v___x_2275_ = l_Lean_Syntax_node3(v___x_2261_, v___x_2271_, v___x_2234_, v___x_2273_, v___x_2274_);
v___x_2276_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2277_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2261_);
lean_ctor_set(v___x_2277_, 1, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_node3(v___x_2261_, v___x_2236_, v___x_2270_, v___x_2275_, v___x_2277_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2278_);
lean_ctor_set(v___x_2279_, 1, v_a_2222_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2280_ = l_Lean_Syntax_getArg(v___x_2258_, v___x_2227_);
lean_dec(v___x_2258_);
v___x_2281_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2280_);
v___x_2282_ = l_Lean_Syntax_isOfKind(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec(v___x_2280_);
v___x_2283_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2283_, 8);
v___x_2285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2283_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2287_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2288_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2289_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2283_);
lean_ctor_set(v___x_2289_, 1, v___x_2286_);
lean_ctor_set(v___x_2289_, 2, v___x_2287_);
lean_ctor_set(v___x_2289_, 3, v___x_2288_);
v___x_2290_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2281_, v___x_2289_);
v___x_2291_ = l_Lean_Syntax_node2(v___x_2283_, v___x_2259_, v___x_2285_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2293_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2283_);
lean_ctor_set(v___x_2294_, 1, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node1(v___x_2283_, v___x_2292_, v___x_2235_);
v___x_2296_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2292_, v___x_2234_, v___x_2294_, v___x_2295_);
v___x_2297_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2298_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2283_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_node3(v___x_2283_, v___x_2236_, v___x_2291_, v___x_2296_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v_a_2222_);
return v___x_2300_;
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; 
v___x_2301_ = l_Lean_Syntax_getArg(v___x_2280_, v___x_2233_);
lean_dec(v___x_2280_);
v___x_2302_ = lean_box(0);
v___x_2303_ = l_Lean_Syntax_matchesIdent(v___x_2301_, v___x_2302_);
lean_dec(v___x_2301_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2304_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2304_, 8);
v___x_2306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2308_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2309_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2310_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2304_);
lean_ctor_set(v___x_2310_, 1, v___x_2307_);
lean_ctor_set(v___x_2310_, 2, v___x_2308_);
lean_ctor_set(v___x_2310_, 3, v___x_2309_);
v___x_2311_ = l_Lean_Syntax_node1(v___x_2304_, v___x_2281_, v___x_2310_);
v___x_2312_ = l_Lean_Syntax_node2(v___x_2304_, v___x_2259_, v___x_2306_, v___x_2311_);
v___x_2313_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2314_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2304_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = l_Lean_Syntax_node1(v___x_2304_, v___x_2313_, v___x_2235_);
v___x_2317_ = l_Lean_Syntax_node3(v___x_2304_, v___x_2313_, v___x_2234_, v___x_2315_, v___x_2316_);
v___x_2318_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2304_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = l_Lean_Syntax_node3(v___x_2304_, v___x_2236_, v___x_2312_, v___x_2317_, v___x_2319_);
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2320_);
lean_ctor_set(v___x_2321_, 1, v_a_2222_);
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2322_ = l_Lean_Syntax_getArg(v___x_2235_, v___x_2227_);
v___x_2323_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2322_);
v___x_2324_ = l_Lean_Syntax_matchesNull(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v___x_2322_);
v___x_2325_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2325_, 8);
v___x_2327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2325_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2329_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2330_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2331_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2325_);
lean_ctor_set(v___x_2331_, 1, v___x_2328_);
lean_ctor_set(v___x_2331_, 2, v___x_2329_);
lean_ctor_set(v___x_2331_, 3, v___x_2330_);
v___x_2332_ = l_Lean_Syntax_node1(v___x_2325_, v___x_2281_, v___x_2331_);
v___x_2333_ = l_Lean_Syntax_node2(v___x_2325_, v___x_2259_, v___x_2327_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2335_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2325_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = l_Lean_Syntax_node1(v___x_2325_, v___x_2334_, v___x_2235_);
v___x_2338_ = l_Lean_Syntax_node3(v___x_2325_, v___x_2334_, v___x_2234_, v___x_2336_, v___x_2337_);
v___x_2339_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2325_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = l_Lean_Syntax_node3(v___x_2325_, v___x_2236_, v___x_2333_, v___x_2338_, v___x_2340_);
v___x_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v_a_2222_);
return v___x_2342_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v___x_2235_);
v___x_2343_ = l_Lean_Syntax_getArg(v___x_2322_, v___x_2233_);
v___x_2344_ = l_Lean_Syntax_getArg(v___x_2322_, v___x_2229_);
lean_dec(v___x_2322_);
v___x_2345_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2346_ = l_Lean_Syntax_getArgs(v___x_2344_);
lean_dec(v___x_2344_);
v___x_2347_ = 0;
v___x_2348_ = l_Lean_SourceInfo_fromRef(v_a_2221_, v___x_2347_);
v___x_2349_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2348_, 8);
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2352_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2353_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2354_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2348_);
lean_ctor_set(v___x_2354_, 1, v___x_2351_);
lean_ctor_set(v___x_2354_, 2, v___x_2352_);
lean_ctor_set(v___x_2354_, 3, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_node1(v___x_2348_, v___x_2281_, v___x_2354_);
v___x_2356_ = l_Lean_Syntax_node2(v___x_2348_, v___x_2259_, v___x_2350_, v___x_2355_);
v___x_2357_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2348_);
lean_ctor_set(v___x_2358_, 1, v___x_2345_);
lean_inc_ref(v___x_2358_);
v___x_2359_ = l_Array_mkArray2___redArg(v___x_2343_, v___x_2358_);
v___x_2360_ = l_Array_append___redArg(v___x_2359_, v___x_2346_);
lean_dec_ref(v___x_2346_);
v___x_2361_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2348_);
lean_ctor_set(v___x_2361_, 1, v___x_2357_);
lean_ctor_set(v___x_2361_, 2, v___x_2360_);
v___x_2362_ = l_Lean_Syntax_node3(v___x_2348_, v___x_2357_, v___x_2234_, v___x_2358_, v___x_2361_);
v___x_2363_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2348_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_node3(v___x_2348_, v___x_2236_, v___x_2356_, v___x_2362_, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_ctor_set(v___x_2366_, 1, v_a_2222_);
return v___x_2366_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk___boxed(lean_object* v_x_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_unexpandProdMk(v_x_2367_, v_a_2368_, v_a_2369_);
lean_dec(v_a_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_unexpandIte(lean_object* v_x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2380_; uint8_t v___x_2381_; 
v___x_2380_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2377_);
v___x_2381_ = l_Lean_Syntax_isOfKind(v_x_2377_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
lean_dec(v_x_2377_);
v___x_2382_ = lean_box(0);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v_a_2379_);
return v___x_2383_;
}
else
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = l_Lean_Syntax_getArg(v_x_2377_, v___x_2384_);
lean_dec(v_x_2377_);
v___x_2386_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2385_);
v___x_2387_ = l_Lean_Syntax_matchesNull(v___x_2385_, v___x_2386_);
if (v___x_2387_ == 0)
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v_a_2379_);
return v___x_2389_;
}
else
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = l_Lean_Syntax_getArg(v___x_2385_, v___x_2390_);
v___x_2392_ = l_Lean_Syntax_getArg(v___x_2385_, v___x_2384_);
v___x_2393_ = lean_unsigned_to_nat(2u);
v___x_2394_ = l_Lean_Syntax_getArg(v___x_2385_, v___x_2393_);
lean_dec(v___x_2385_);
v___x_2395_ = 0;
v___x_2396_ = l_Lean_SourceInfo_fromRef(v_a_2378_, v___x_2395_);
v___x_2397_ = ((lean_object*)(l_unexpandIte___closed__1));
v___x_2398_ = ((lean_object*)(l_unexpandIte___closed__2));
lean_inc_n(v___x_2396_, 3);
v___x_2399_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_unexpandIte___closed__3));
v___x_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2396_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = ((lean_object*)(l_unexpandIte___closed__4));
v___x_2403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2396_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = l_Lean_Syntax_node6(v___x_2396_, v___x_2397_, v___x_2399_, v___x_2391_, v___x_2401_, v___x_2392_, v___x_2403_, v___x_2394_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
lean_ctor_set(v___x_2405_, 1, v_a_2379_);
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandIte___boxed(lean_object* v_x_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_unexpandIte(v_x_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2407_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec(lean_object* v_x_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2417_);
v___x_2421_ = l_Lean_Syntax_isOfKind(v_x_2417_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
lean_dec(v_x_2417_);
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
lean_ctor_set(v___x_2423_, 1, v_a_2419_);
return v___x_2423_;
}
else
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2424_ = lean_unsigned_to_nat(1u);
v___x_2425_ = l_Lean_Syntax_getArg(v_x_2417_, v___x_2424_);
lean_dec(v_x_2417_);
v___x_2426_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2425_);
v___x_2427_ = l_Lean_Syntax_matchesNull(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
lean_ctor_set(v___x_2429_, 1, v_a_2419_);
return v___x_2429_;
}
else
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2430_ = lean_unsigned_to_nat(0u);
v___x_2431_ = l_Lean_Syntax_getArg(v___x_2425_, v___x_2430_);
v___x_2432_ = l_Lean_Syntax_getArg(v___x_2425_, v___x_2424_);
lean_dec(v___x_2425_);
v___x_2433_ = 0;
v___x_2434_ = l_Lean_SourceInfo_fromRef(v_a_2418_, v___x_2433_);
v___x_2435_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2436_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc_n(v___x_2434_, 2);
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2434_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2439_ = l_Lean_Syntax_node1(v___x_2434_, v___x_2438_, v___x_2431_);
v___x_2440_ = l_Lean_Syntax_node3(v___x_2434_, v___x_2435_, v___x_2432_, v___x_2437_, v___x_2439_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v_a_2419_);
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec___boxed(lean_object* v_x_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_unexpandEqNDRec(v_x_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec(lean_object* v_x_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2449_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2446_);
v___x_2450_ = l_Lean_Syntax_isOfKind(v_x_2446_, v___x_2449_);
if (v___x_2450_ == 0)
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_dec(v_x_2446_);
v___x_2451_ = lean_box(0);
v___x_2452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2451_);
lean_ctor_set(v___x_2452_, 1, v_a_2448_);
return v___x_2452_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2453_ = lean_unsigned_to_nat(1u);
v___x_2454_ = l_Lean_Syntax_getArg(v_x_2446_, v___x_2453_);
lean_dec(v_x_2446_);
v___x_2455_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2454_);
v___x_2456_ = l_Lean_Syntax_matchesNull(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v___x_2454_);
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_a_2448_);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = l_Lean_Syntax_getArg(v___x_2454_, v___x_2459_);
v___x_2461_ = l_Lean_Syntax_getArg(v___x_2454_, v___x_2453_);
lean_dec(v___x_2454_);
v___x_2462_ = 0;
v___x_2463_ = l_Lean_SourceInfo_fromRef(v_a_2447_, v___x_2462_);
v___x_2464_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2465_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc_n(v___x_2463_, 2);
v___x_2466_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2466_, 0, v___x_2463_);
lean_ctor_set(v___x_2466_, 1, v___x_2465_);
v___x_2467_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2468_ = l_Lean_Syntax_node1(v___x_2463_, v___x_2467_, v___x_2460_);
v___x_2469_ = l_Lean_Syntax_node3(v___x_2463_, v___x_2464_, v___x_2461_, v___x_2466_, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v_a_2448_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec___boxed(lean_object* v_x_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_unexpandEqRec(v_x_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2472_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_unexpandExists(lean_object* v_x_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v___x_2488_; uint8_t v___x_2489_; 
v___x_2488_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2485_);
v___x_2489_ = l_Lean_Syntax_isOfKind(v_x_2485_, v___x_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_x_2485_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
lean_ctor_set(v___x_2491_, 1, v_a_2487_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = l_Lean_Syntax_getArg(v_x_2485_, v___x_2492_);
lean_dec(v_x_2485_);
lean_inc(v___x_2493_);
v___x_2494_ = l_Lean_Syntax_matchesNull(v___x_2493_, v___x_2492_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v___x_2493_);
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v_a_2487_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; uint8_t v___x_2500_; 
v___x_2497_ = lean_unsigned_to_nat(0u);
v___x_2498_ = l_Lean_Syntax_getArg(v___x_2493_, v___x_2497_);
lean_dec(v___x_2493_);
v___x_2499_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2498_);
v___x_2500_ = l_Lean_Syntax_isOfKind(v___x_2498_, v___x_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v___x_2502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2501_);
lean_ctor_set(v___x_2502_, 1, v_a_2487_);
return v___x_2502_;
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2503_ = l_Lean_Syntax_getArg(v___x_2498_, v___x_2492_);
lean_dec(v___x_2498_);
v___x_2504_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2503_);
v___x_2505_ = l_Lean_Syntax_isOfKind(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v_a_2487_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2508_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2497_);
lean_inc(v___x_2508_);
v___x_2509_ = l_Lean_Syntax_matchesNull(v___x_2508_, v___x_2492_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2508_);
lean_dec(v___x_2503_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_a_2487_);
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2512_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2497_);
lean_dec(v___x_2508_);
v___x_2513_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2512_);
v___x_2514_ = l_Lean_Syntax_isOfKind(v___x_2512_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2512_);
v___x_2516_ = l_Lean_Syntax_isOfKind(v___x_2512_, v___x_2515_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v_a_2487_);
return v___x_2518_;
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2519_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2497_);
v___x_2520_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2519_);
v___x_2521_ = l_Lean_Syntax_isOfKind(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v___x_2519_);
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2522_ = lean_box(0);
v___x_2523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2522_);
lean_ctor_set(v___x_2523_, 1, v_a_2487_);
return v___x_2523_;
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2524_ = l_Lean_Syntax_getArg(v___x_2519_, v___x_2492_);
lean_dec(v___x_2519_);
v___x_2525_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2524_);
v___x_2526_ = l_Lean_Syntax_isOfKind(v___x_2524_, v___x_2525_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec(v___x_2524_);
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2527_ = lean_box(0);
v___x_2528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
lean_ctor_set(v___x_2528_, 1, v_a_2487_);
return v___x_2528_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2529_ = l_Lean_Syntax_getArg(v___x_2524_, v___x_2497_);
lean_dec(v___x_2524_);
v___x_2530_ = lean_box(0);
v___x_2531_ = l_Lean_Syntax_matchesIdent(v___x_2529_, v___x_2530_);
lean_dec(v___x_2529_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2532_ = lean_box(0);
v___x_2533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_a_2487_);
return v___x_2533_;
}
else
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2492_);
lean_inc(v___x_2534_);
v___x_2535_ = l_Lean_Syntax_isOfKind(v___x_2534_, v___x_2513_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v___x_2534_);
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v_a_2487_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_unsigned_to_nat(3u);
v___x_2539_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2538_);
lean_dec(v___x_2512_);
lean_inc(v___x_2539_);
v___x_2540_ = l_Lean_Syntax_matchesNull(v___x_2539_, v___x_2492_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v___x_2539_);
lean_dec(v___x_2534_);
lean_dec(v___x_2503_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v_a_2487_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2543_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2492_);
v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2543_, v___x_2497_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2539_);
lean_dec(v___x_2534_);
lean_dec(v___x_2503_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v_a_2487_);
return v___x_2546_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2547_ = l_Lean_Syntax_getArg(v___x_2539_, v___x_2497_);
lean_dec(v___x_2539_);
v___x_2548_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2538_);
lean_dec(v___x_2503_);
v___x_2549_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2514_);
v___x_2550_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_2551_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2549_, 10);
v___x_2552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2549_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2554_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2555_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2556_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_2557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2549_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2559_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2558_, v___x_2534_);
v___x_2560_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2554_, v___x_2559_);
v___x_2561_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2562_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2549_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2549_);
lean_ctor_set(v___x_2564_, 1, v___x_2563_);
v___x_2565_ = l_Lean_Syntax_node5(v___x_2549_, v___x_2555_, v___x_2557_, v___x_2560_, v___x_2562_, v___x_2547_, v___x_2564_);
v___x_2566_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2554_, v___x_2565_);
v___x_2567_ = l_Lean_Syntax_node1(v___x_2549_, v___x_2553_, v___x_2566_);
v___x_2568_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2549_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = l_Lean_Syntax_node4(v___x_2549_, v___x_2550_, v___x_2552_, v___x_2567_, v___x_2569_, v___x_2548_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_ctor_set(v___x_2571_, 1, v_a_2487_);
return v___x_2571_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2492_);
v___x_2573_ = l_Lean_Syntax_matchesNull(v___x_2572_, v___x_2497_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v___x_2512_);
lean_dec(v___x_2503_);
v___x_2574_ = lean_box(0);
v___x_2575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_a_2487_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2576_ = lean_unsigned_to_nat(3u);
v___x_2577_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2576_);
lean_dec(v___x_2503_);
v___x_2578_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v___x_2577_);
v___x_2579_ = l_Lean_Syntax_isOfKind(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2580_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2579_);
v___x_2581_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2580_, 7);
v___x_2582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2580_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2584_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2585_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2586_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2587_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2586_, v___x_2512_);
v___x_2588_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2585_, v___x_2587_);
v___x_2589_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2580_);
lean_ctor_set(v___x_2590_, 1, v___x_2585_);
lean_ctor_set(v___x_2590_, 2, v___x_2589_);
v___x_2591_ = l_Lean_Syntax_node2(v___x_2580_, v___x_2584_, v___x_2588_, v___x_2590_);
v___x_2592_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2583_, v___x_2591_);
v___x_2593_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2580_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = l_Lean_Syntax_node4(v___x_2580_, v___x_2578_, v___x_2582_, v___x_2592_, v___x_2594_, v___x_2577_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v_a_2487_);
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2597_ = l_Lean_Syntax_getArg(v___x_2577_, v___x_2492_);
v___x_2598_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
lean_inc(v___x_2597_);
v___x_2599_ = l_Lean_Syntax_isOfKind(v___x_2597_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec(v___x_2597_);
v___x_2600_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2600_, 7);
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2604_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2605_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2606_ = l_Lean_Syntax_node1(v___x_2600_, v___x_2605_, v___x_2512_);
v___x_2607_ = l_Lean_Syntax_node1(v___x_2600_, v___x_2604_, v___x_2606_);
v___x_2608_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2600_);
lean_ctor_set(v___x_2609_, 1, v___x_2604_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
v___x_2610_ = l_Lean_Syntax_node2(v___x_2600_, v___x_2603_, v___x_2607_, v___x_2609_);
v___x_2611_ = l_Lean_Syntax_node1(v___x_2600_, v___x_2598_, v___x_2610_);
v___x_2612_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2613_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2600_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = l_Lean_Syntax_node4(v___x_2600_, v___x_2578_, v___x_2602_, v___x_2611_, v___x_2613_, v___x_2577_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2614_);
lean_ctor_set(v___x_2615_, 1, v_a_2487_);
return v___x_2615_;
}
else
{
lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2616_ = l_Lean_Syntax_getArg(v___x_2597_, v___x_2497_);
lean_dec(v___x_2597_);
v___x_2617_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
lean_inc(v___x_2616_);
v___x_2618_ = l_Lean_Syntax_isOfKind(v___x_2616_, v___x_2617_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
lean_dec(v___x_2616_);
v___x_2619_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2618_);
v___x_2620_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2619_, 7);
v___x_2621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2619_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2623_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2624_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2623_, v___x_2512_);
v___x_2625_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2622_, v___x_2624_);
v___x_2626_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2627_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2619_);
lean_ctor_set(v___x_2627_, 1, v___x_2622_);
lean_ctor_set(v___x_2627_, 2, v___x_2626_);
v___x_2628_ = l_Lean_Syntax_node2(v___x_2619_, v___x_2617_, v___x_2625_, v___x_2627_);
v___x_2629_ = l_Lean_Syntax_node1(v___x_2619_, v___x_2598_, v___x_2628_);
v___x_2630_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2631_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2619_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = l_Lean_Syntax_node4(v___x_2619_, v___x_2578_, v___x_2621_, v___x_2629_, v___x_2631_, v___x_2577_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v_a_2487_);
return v___x_2633_;
}
else
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = l_Lean_Syntax_getArg(v___x_2616_, v___x_2492_);
v___x_2635_ = l_Lean_Syntax_matchesNull(v___x_2634_, v___x_2497_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec(v___x_2616_);
v___x_2636_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2636_, 7);
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2636_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2640_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2641_ = l_Lean_Syntax_node1(v___x_2636_, v___x_2640_, v___x_2512_);
v___x_2642_ = l_Lean_Syntax_node1(v___x_2636_, v___x_2639_, v___x_2641_);
v___x_2643_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2636_);
lean_ctor_set(v___x_2644_, 1, v___x_2639_);
lean_ctor_set(v___x_2644_, 2, v___x_2643_);
v___x_2645_ = l_Lean_Syntax_node2(v___x_2636_, v___x_2617_, v___x_2642_, v___x_2644_);
v___x_2646_ = l_Lean_Syntax_node1(v___x_2636_, v___x_2598_, v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2636_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_Syntax_node4(v___x_2636_, v___x_2578_, v___x_2638_, v___x_2646_, v___x_2648_, v___x_2577_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2649_);
lean_ctor_set(v___x_2650_, 1, v_a_2487_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_xs_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2651_ = l_Lean_Syntax_getArg(v___x_2616_, v___x_2497_);
lean_dec(v___x_2616_);
v___x_2652_ = l_Lean_Syntax_getArg(v___x_2577_, v___x_2576_);
lean_dec(v___x_2577_);
v___x_2653_ = ((lean_object*)(l_unexpandExists___closed__3));
v_xs_2654_ = l_Lean_Syntax_getArgs(v___x_2651_);
lean_dec(v___x_2651_);
v___x_2655_ = 0;
v___x_2656_ = l_Lean_SourceInfo_fromRef(v_a_2486_, v___x_2655_);
v___x_2657_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2656_, 7);
v___x_2658_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2657_);
v___x_2659_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2660_ = l_Lean_Syntax_node1(v___x_2656_, v___x_2653_, v___x_2512_);
v___x_2661_ = l_Array_mkArray1___redArg(v___x_2660_);
v___x_2662_ = l_Array_append___redArg(v___x_2661_, v_xs_2654_);
lean_dec_ref(v_xs_2654_);
v___x_2663_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2656_);
lean_ctor_set(v___x_2663_, 1, v___x_2659_);
lean_ctor_set(v___x_2663_, 2, v___x_2662_);
v___x_2664_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2656_);
lean_ctor_set(v___x_2665_, 1, v___x_2659_);
lean_ctor_set(v___x_2665_, 2, v___x_2664_);
v___x_2666_ = l_Lean_Syntax_node2(v___x_2656_, v___x_2617_, v___x_2663_, v___x_2665_);
v___x_2667_ = l_Lean_Syntax_node1(v___x_2656_, v___x_2598_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2656_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_node4(v___x_2656_, v___x_2578_, v___x_2658_, v___x_2667_, v___x_2669_, v___x_2652_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v_a_2487_);
return v___x_2671_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandExists___boxed(lean_object* v_x_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_unexpandExists(v_x_2672_, v_a_2673_, v_a_2674_);
lean_dec(v_a_2673_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_unexpandSigma(lean_object* v_x_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v___x_2680_; uint8_t v___x_2681_; 
v___x_2680_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2677_);
v___x_2681_ = l_Lean_Syntax_isOfKind(v_x_2677_, v___x_2680_);
if (v___x_2681_ == 0)
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
lean_dec(v_x_2677_);
v___x_2682_ = lean_box(0);
v___x_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v_a_2679_);
return v___x_2683_;
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = l_Lean_Syntax_getArg(v_x_2677_, v___x_2684_);
lean_dec(v_x_2677_);
lean_inc(v___x_2685_);
v___x_2686_ = l_Lean_Syntax_matchesNull(v___x_2685_, v___x_2684_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
lean_dec(v___x_2685_);
v___x_2687_ = lean_box(0);
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v_a_2679_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = l_Lean_Syntax_getArg(v___x_2685_, v___x_2689_);
lean_dec(v___x_2685_);
v___x_2691_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2690_);
v___x_2692_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
lean_dec(v___x_2690_);
v___x_2693_ = lean_box(0);
v___x_2694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_a_2679_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2695_ = l_Lean_Syntax_getArg(v___x_2690_, v___x_2684_);
lean_dec(v___x_2690_);
v___x_2696_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2695_);
v___x_2697_ = l_Lean_Syntax_isOfKind(v___x_2695_, v___x_2696_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec(v___x_2695_);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v_a_2679_);
return v___x_2699_;
}
else
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = l_Lean_Syntax_getArg(v___x_2695_, v___x_2689_);
lean_inc(v___x_2700_);
v___x_2701_ = l_Lean_Syntax_matchesNull(v___x_2700_, v___x_2684_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec(v___x_2700_);
lean_dec(v___x_2695_);
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v_a_2679_);
return v___x_2703_;
}
else
{
lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2704_ = l_Lean_Syntax_getArg(v___x_2700_, v___x_2689_);
lean_dec(v___x_2700_);
v___x_2705_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2704_);
v___x_2706_ = l_Lean_Syntax_isOfKind(v___x_2704_, v___x_2705_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v___x_2704_);
lean_dec(v___x_2695_);
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v_a_2679_);
return v___x_2708_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v___x_2709_ = l_Lean_Syntax_getArg(v___x_2704_, v___x_2689_);
v___x_2710_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2709_);
v___x_2711_ = l_Lean_Syntax_isOfKind(v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v___x_2709_);
lean_dec(v___x_2704_);
lean_dec(v___x_2695_);
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
lean_ctor_set(v___x_2713_, 1, v_a_2679_);
return v___x_2713_;
}
else
{
lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2714_ = l_Lean_Syntax_getArg(v___x_2709_, v___x_2684_);
lean_dec(v___x_2709_);
v___x_2715_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2714_);
v___x_2716_ = l_Lean_Syntax_isOfKind(v___x_2714_, v___x_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
lean_dec(v___x_2714_);
lean_dec(v___x_2704_);
lean_dec(v___x_2695_);
v___x_2717_ = lean_box(0);
v___x_2718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_a_2679_);
return v___x_2718_;
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2719_ = l_Lean_Syntax_getArg(v___x_2714_, v___x_2689_);
lean_dec(v___x_2714_);
v___x_2720_ = lean_box(0);
v___x_2721_ = l_Lean_Syntax_matchesIdent(v___x_2719_, v___x_2720_);
lean_dec(v___x_2719_);
if (v___x_2721_ == 0)
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v___x_2704_);
lean_dec(v___x_2695_);
v___x_2722_ = lean_box(0);
v___x_2723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_a_2679_);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2724_ = l_Lean_Syntax_getArg(v___x_2704_, v___x_2684_);
v___x_2725_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2724_);
v___x_2726_ = l_Lean_Syntax_isOfKind(v___x_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_dec(v___x_2724_);
lean_dec(v___x_2704_);
lean_dec(v___x_2695_);
v___x_2727_ = lean_box(0);
v___x_2728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2728_, 0, v___x_2727_);
lean_ctor_set(v___x_2728_, 1, v_a_2679_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v___x_2729_ = lean_unsigned_to_nat(3u);
v___x_2730_ = l_Lean_Syntax_getArg(v___x_2704_, v___x_2729_);
lean_dec(v___x_2704_);
lean_inc(v___x_2730_);
v___x_2731_ = l_Lean_Syntax_matchesNull(v___x_2730_, v___x_2684_);
if (v___x_2731_ == 0)
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec(v___x_2730_);
lean_dec(v___x_2724_);
lean_dec(v___x_2695_);
v___x_2732_ = lean_box(0);
v___x_2733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_a_2679_);
return v___x_2733_;
}
else
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = l_Lean_Syntax_getArg(v___x_2695_, v___x_2684_);
v___x_2735_ = l_Lean_Syntax_matchesNull(v___x_2734_, v___x_2689_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v___x_2730_);
lean_dec(v___x_2724_);
lean_dec(v___x_2695_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_a_2679_);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2738_ = l_Lean_Syntax_getArg(v___x_2730_, v___x_2689_);
lean_dec(v___x_2730_);
v___x_2739_ = l_Lean_Syntax_getArg(v___x_2695_, v___x_2729_);
lean_dec(v___x_2695_);
v___x_2740_ = 0;
v___x_2741_ = l_Lean_SourceInfo_fromRef(v_a_2678_, v___x_2740_);
v___x_2742_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_2743_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2744_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2741_, 7);
v___x_2745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2747_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2748_ = l_Lean_Syntax_node1(v___x_2741_, v___x_2747_, v___x_2724_);
v___x_2749_ = l_Lean_Syntax_node1(v___x_2741_, v___x_2746_, v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2741_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2741_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_Syntax_node5(v___x_2741_, v___x_2743_, v___x_2745_, v___x_2749_, v___x_2751_, v___x_2738_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l_unexpandSigma___closed__0));
v___x_2756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2741_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_Syntax_node3(v___x_2741_, v___x_2742_, v___x_2754_, v___x_2756_, v___x_2739_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
lean_ctor_set(v___x_2758_, 1, v_a_2679_);
return v___x_2758_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandSigma___boxed(lean_object* v_x_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_unexpandSigma(v_x_2759_, v_a_2760_, v_a_2761_);
lean_dec(v_a_2760_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_unexpandPSigma(lean_object* v_x_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_){
_start:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2767_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2764_);
v___x_2768_ = l_Lean_Syntax_isOfKind(v_x_2764_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v_x_2764_);
v___x_2769_ = lean_box(0);
v___x_2770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
lean_ctor_set(v___x_2770_, 1, v_a_2766_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2771_ = lean_unsigned_to_nat(1u);
v___x_2772_ = l_Lean_Syntax_getArg(v_x_2764_, v___x_2771_);
lean_dec(v_x_2764_);
lean_inc(v___x_2772_);
v___x_2773_ = l_Lean_Syntax_matchesNull(v___x_2772_, v___x_2771_);
if (v___x_2773_ == 0)
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v___x_2772_);
v___x_2774_ = lean_box(0);
v___x_2775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2774_);
lean_ctor_set(v___x_2775_, 1, v_a_2766_);
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = l_Lean_Syntax_getArg(v___x_2772_, v___x_2776_);
lean_dec(v___x_2772_);
v___x_2778_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2777_);
v___x_2779_ = l_Lean_Syntax_isOfKind(v___x_2777_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2780_);
lean_ctor_set(v___x_2781_, 1, v_a_2766_);
return v___x_2781_;
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = l_Lean_Syntax_getArg(v___x_2777_, v___x_2771_);
lean_dec(v___x_2777_);
v___x_2783_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2782_);
v___x_2784_ = l_Lean_Syntax_isOfKind(v___x_2782_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_a_2766_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2787_ = l_Lean_Syntax_getArg(v___x_2782_, v___x_2776_);
lean_inc(v___x_2787_);
v___x_2788_ = l_Lean_Syntax_matchesNull(v___x_2787_, v___x_2771_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec(v___x_2787_);
lean_dec(v___x_2782_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v_a_2766_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v___x_2791_ = l_Lean_Syntax_getArg(v___x_2787_, v___x_2776_);
lean_dec(v___x_2787_);
v___x_2792_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2791_);
v___x_2793_ = l_Lean_Syntax_isOfKind(v___x_2791_, v___x_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec(v___x_2791_);
lean_dec(v___x_2782_);
v___x_2794_ = lean_box(0);
v___x_2795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
lean_ctor_set(v___x_2795_, 1, v_a_2766_);
return v___x_2795_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2796_ = l_Lean_Syntax_getArg(v___x_2791_, v___x_2776_);
v___x_2797_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2796_);
v___x_2798_ = l_Lean_Syntax_isOfKind(v___x_2796_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
lean_dec(v___x_2796_);
lean_dec(v___x_2791_);
lean_dec(v___x_2782_);
v___x_2799_ = lean_box(0);
v___x_2800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
lean_ctor_set(v___x_2800_, 1, v_a_2766_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = l_Lean_Syntax_getArg(v___x_2796_, v___x_2771_);
lean_dec(v___x_2796_);
v___x_2802_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2801_);
v___x_2803_ = l_Lean_Syntax_isOfKind(v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
lean_dec(v___x_2801_);
lean_dec(v___x_2791_);
lean_dec(v___x_2782_);
v___x_2804_ = lean_box(0);
v___x_2805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2804_);
lean_ctor_set(v___x_2805_, 1, v_a_2766_);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; uint8_t v___x_2808_; 
v___x_2806_ = l_Lean_Syntax_getArg(v___x_2801_, v___x_2776_);
lean_dec(v___x_2801_);
v___x_2807_ = lean_box(0);
v___x_2808_ = l_Lean_Syntax_matchesIdent(v___x_2806_, v___x_2807_);
lean_dec(v___x_2806_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
lean_dec(v___x_2791_);
lean_dec(v___x_2782_);
v___x_2809_ = lean_box(0);
v___x_2810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2809_);
lean_ctor_set(v___x_2810_, 1, v_a_2766_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = l_Lean_Syntax_getArg(v___x_2791_, v___x_2771_);
v___x_2812_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2811_);
v___x_2813_ = l_Lean_Syntax_isOfKind(v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
lean_dec(v___x_2811_);
lean_dec(v___x_2791_);
lean_dec(v___x_2782_);
v___x_2814_ = lean_box(0);
v___x_2815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_a_2766_);
return v___x_2815_;
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v___x_2816_ = lean_unsigned_to_nat(3u);
v___x_2817_ = l_Lean_Syntax_getArg(v___x_2791_, v___x_2816_);
lean_dec(v___x_2791_);
lean_inc(v___x_2817_);
v___x_2818_ = l_Lean_Syntax_matchesNull(v___x_2817_, v___x_2771_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v___x_2817_);
lean_dec(v___x_2811_);
lean_dec(v___x_2782_);
v___x_2819_ = lean_box(0);
v___x_2820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2819_);
lean_ctor_set(v___x_2820_, 1, v_a_2766_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = l_Lean_Syntax_getArg(v___x_2782_, v___x_2771_);
v___x_2822_ = l_Lean_Syntax_matchesNull(v___x_2821_, v___x_2776_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v___x_2817_);
lean_dec(v___x_2811_);
lean_dec(v___x_2782_);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
lean_ctor_set(v___x_2824_, 1, v_a_2766_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v___x_2825_ = l_Lean_Syntax_getArg(v___x_2817_, v___x_2776_);
lean_dec(v___x_2817_);
v___x_2826_ = l_Lean_Syntax_getArg(v___x_2782_, v___x_2816_);
lean_dec(v___x_2782_);
v___x_2827_ = 0;
v___x_2828_ = l_Lean_SourceInfo_fromRef(v_a_2765_, v___x_2827_);
v___x_2829_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_2830_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2831_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2828_, 7);
v___x_2832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2828_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
v___x_2833_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2834_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2835_ = l_Lean_Syntax_node1(v___x_2828_, v___x_2834_, v___x_2811_);
v___x_2836_ = l_Lean_Syntax_node1(v___x_2828_, v___x_2833_, v___x_2835_);
v___x_2837_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2828_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2828_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_Syntax_node5(v___x_2828_, v___x_2830_, v___x_2832_, v___x_2836_, v___x_2838_, v___x_2825_, v___x_2840_);
v___x_2842_ = ((lean_object*)(l_unexpandPSigma___closed__0));
v___x_2843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2828_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_Syntax_node3(v___x_2828_, v___x_2829_, v___x_2841_, v___x_2843_, v___x_2826_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v_a_2766_);
return v___x_2845_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandPSigma___boxed(lean_object* v_x_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_unexpandPSigma(v_x_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_unexpandSubtype(lean_object* v_x_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2859_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2856_);
v___x_2860_ = l_Lean_Syntax_isOfKind(v_x_2856_, v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec(v_x_2856_);
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v_a_2858_);
return v___x_2862_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = l_Lean_Syntax_getArg(v_x_2856_, v___x_2863_);
lean_dec(v_x_2856_);
lean_inc(v___x_2864_);
v___x_2865_ = l_Lean_Syntax_matchesNull(v___x_2864_, v___x_2863_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec(v___x_2864_);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
lean_ctor_set(v___x_2867_, 1, v_a_2858_);
return v___x_2867_;
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2868_ = lean_unsigned_to_nat(0u);
v___x_2869_ = l_Lean_Syntax_getArg(v___x_2864_, v___x_2868_);
lean_dec(v___x_2864_);
v___x_2870_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2869_);
v___x_2871_ = l_Lean_Syntax_isOfKind(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v___x_2873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2872_);
lean_ctor_set(v___x_2873_, 1, v_a_2858_);
return v___x_2873_;
}
else
{
lean_object* v___x_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = l_Lean_Syntax_getArg(v___x_2869_, v___x_2863_);
lean_dec(v___x_2869_);
v___x_2875_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2874_);
v___x_2876_ = l_Lean_Syntax_isOfKind(v___x_2874_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2877_);
lean_ctor_set(v___x_2878_, 1, v_a_2858_);
return v___x_2878_;
}
else
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2868_);
lean_inc(v___x_2879_);
v___x_2880_ = l_Lean_Syntax_matchesNull(v___x_2879_, v___x_2863_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v___x_2879_);
lean_dec(v___x_2874_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v_a_2858_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v___x_2883_ = l_Lean_Syntax_getArg(v___x_2879_, v___x_2868_);
lean_dec(v___x_2879_);
v___x_2884_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2883_);
v___x_2885_ = l_Lean_Syntax_isOfKind(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; uint8_t v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2883_);
v___x_2887_ = l_Lean_Syntax_isOfKind(v___x_2883_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2888_ = lean_box(0);
v___x_2889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2888_);
lean_ctor_set(v___x_2889_, 1, v_a_2858_);
return v___x_2889_;
}
else
{
lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2890_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2863_);
v___x_2891_ = l_Lean_Syntax_matchesNull(v___x_2890_, v___x_2868_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2892_ = lean_box(0);
v___x_2893_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2892_);
lean_ctor_set(v___x_2893_, 1, v_a_2858_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2894_ = lean_unsigned_to_nat(3u);
v___x_2895_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2894_);
lean_dec(v___x_2874_);
v___x_2896_ = l_Lean_SourceInfo_fromRef(v_a_2857_, v___x_2885_);
v___x_2897_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2898_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2896_, 4);
v___x_2899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2899_, 0, v___x_2896_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
v___x_2900_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2901_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2896_);
lean_ctor_set(v___x_2902_, 1, v___x_2900_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
v___x_2903_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2896_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2906_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2896_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = l_Lean_Syntax_node6(v___x_2896_, v___x_2897_, v___x_2899_, v___x_2883_, v___x_2902_, v___x_2904_, v___x_2895_, v___x_2906_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
lean_ctor_set(v___x_2908_, 1, v_a_2858_);
return v___x_2908_;
}
}
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2909_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2868_);
v___x_2910_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2909_);
v___x_2911_ = l_Lean_Syntax_isOfKind(v___x_2909_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v___x_2909_);
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v_a_2858_);
return v___x_2913_;
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = l_Lean_Syntax_getArg(v___x_2909_, v___x_2863_);
lean_dec(v___x_2909_);
v___x_2915_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2914_);
v___x_2916_ = l_Lean_Syntax_isOfKind(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_dec(v___x_2914_);
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_a_2858_);
return v___x_2918_;
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2919_ = l_Lean_Syntax_getArg(v___x_2914_, v___x_2868_);
lean_dec(v___x_2914_);
v___x_2920_ = lean_box(0);
v___x_2921_ = l_Lean_Syntax_matchesIdent(v___x_2919_, v___x_2920_);
lean_dec(v___x_2919_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v_a_2858_);
return v___x_2923_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2863_);
v___x_2925_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2924_);
v___x_2926_ = l_Lean_Syntax_isOfKind(v___x_2924_, v___x_2925_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec(v___x_2924_);
lean_dec(v___x_2883_);
lean_dec(v___x_2874_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v_a_2858_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = lean_unsigned_to_nat(3u);
v___x_2930_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2929_);
lean_dec(v___x_2883_);
lean_inc(v___x_2930_);
v___x_2931_ = l_Lean_Syntax_matchesNull(v___x_2930_, v___x_2863_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v___x_2930_);
lean_dec(v___x_2924_);
lean_dec(v___x_2874_);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v_a_2858_);
return v___x_2933_;
}
else
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2863_);
v___x_2935_ = l_Lean_Syntax_matchesNull(v___x_2934_, v___x_2868_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
lean_dec(v___x_2930_);
lean_dec(v___x_2924_);
lean_dec(v___x_2874_);
v___x_2936_ = lean_box(0);
v___x_2937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
lean_ctor_set(v___x_2937_, 1, v_a_2858_);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2938_ = l_Lean_Syntax_getArg(v___x_2930_, v___x_2868_);
lean_dec(v___x_2930_);
v___x_2939_ = l_Lean_Syntax_getArg(v___x_2874_, v___x_2929_);
lean_dec(v___x_2874_);
v___x_2940_ = 0;
v___x_2941_ = l_Lean_SourceInfo_fromRef(v_a_2857_, v___x_2940_);
v___x_2942_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2943_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2941_, 5);
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2941_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2946_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2941_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_Syntax_node2(v___x_2941_, v___x_2945_, v___x_2947_, v___x_2938_);
v___x_2949_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2941_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2941_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = l_Lean_Syntax_node6(v___x_2941_, v___x_2942_, v___x_2944_, v___x_2924_, v___x_2948_, v___x_2950_, v___x_2939_, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_a_2858_);
return v___x_2954_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandSubtype___boxed(lean_object* v_x_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_unexpandSubtype(v_x_2955_, v_a_2956_, v_a_2957_);
lean_dec(v_a_2956_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax(lean_object* v_x_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2959_);
v___x_2963_ = l_Lean_Syntax_isOfKind(v_x_2959_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
lean_dec(v_x_2959_);
v___x_2964_ = lean_box(0);
v___x_2965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_a_2961_);
return v___x_2965_;
}
else
{
lean_object* v___x_2966_; lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2966_ = lean_unsigned_to_nat(1u);
v___x_2967_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2966_);
lean_inc(v___x_2967_);
v___x_2968_ = l_Lean_Syntax_matchesNull(v___x_2967_, v___x_2966_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec(v___x_2967_);
lean_dec(v_x_2959_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2961_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = l_Lean_Syntax_getArg(v___x_2967_, v___x_2971_);
lean_dec(v___x_2967_);
v___x_2973_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2972_);
v___x_2974_ = l_Lean_Syntax_isOfKind(v___x_2972_, v___x_2973_);
if (v___x_2974_ == 0)
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
lean_dec(v___x_2972_);
lean_dec(v_x_2959_);
v___x_2975_ = lean_box(0);
v___x_2976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v_a_2961_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; uint8_t v___x_2978_; 
v___x_2977_ = l_Lean_Syntax_getArg(v___x_2972_, v___x_2966_);
lean_dec(v___x_2972_);
lean_inc(v___x_2977_);
v___x_2978_ = l_Lean_Syntax_matchesNull(v___x_2977_, v___x_2966_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec(v___x_2977_);
lean_dec(v_x_2959_);
v___x_2979_ = lean_box(0);
v___x_2980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2980_, 0, v___x_2979_);
lean_ctor_set(v___x_2980_, 1, v_a_2961_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2981_ = l_Lean_Syntax_getArg(v_x_2959_, v___x_2971_);
lean_dec(v_x_2959_);
v___x_2982_ = l_Lean_Syntax_getArg(v___x_2977_, v___x_2971_);
lean_dec(v___x_2977_);
v___x_2983_ = 0;
v___x_2984_ = l_Lean_SourceInfo_fromRef(v_a_2960_, v___x_2983_);
v___x_2985_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_2984_);
v___x_2986_ = l_Lean_Syntax_node1(v___x_2984_, v___x_2985_, v___x_2982_);
v___x_2987_ = l_Lean_Syntax_node2(v___x_2984_, v___x_2962_, v___x_2981_, v___x_2986_);
v___x_2988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
lean_ctor_set(v___x_2988_, 1, v_a_2961_);
return v___x_2988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax___boxed(lean_object* v_x_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_unexpandTSyntax(v_x_2989_, v_a_2990_, v_a_2991_);
lean_dec(v_a_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray(lean_object* v_x_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v___x_2996_; uint8_t v___x_2997_; 
v___x_2996_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2993_);
v___x_2997_ = l_Lean_Syntax_isOfKind(v_x_2993_, v___x_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec(v_x_2993_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v_a_2995_);
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3000_ = lean_unsigned_to_nat(1u);
v___x_3001_ = l_Lean_Syntax_getArg(v_x_2993_, v___x_3000_);
lean_inc(v___x_3001_);
v___x_3002_ = l_Lean_Syntax_matchesNull(v___x_3001_, v___x_3000_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v___x_3001_);
lean_dec(v_x_2993_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v_a_2995_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = l_Lean_Syntax_getArg(v___x_3001_, v___x_3005_);
lean_dec(v___x_3001_);
v___x_3007_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_3006_);
v___x_3008_ = l_Lean_Syntax_isOfKind(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v___x_3006_);
lean_dec(v_x_2993_);
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_a_2995_);
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = l_Lean_Syntax_getArg(v___x_3006_, v___x_3000_);
lean_dec(v___x_3006_);
lean_inc(v___x_3011_);
v___x_3012_ = l_Lean_Syntax_matchesNull(v___x_3011_, v___x_3000_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec(v___x_3011_);
lean_dec(v_x_2993_);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
lean_ctor_set(v___x_3014_, 1, v_a_2995_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3015_ = l_Lean_Syntax_getArg(v_x_2993_, v___x_3005_);
lean_dec(v_x_2993_);
v___x_3016_ = l_Lean_Syntax_getArg(v___x_3011_, v___x_3005_);
lean_dec(v___x_3011_);
v___x_3017_ = 0;
v___x_3018_ = l_Lean_SourceInfo_fromRef(v_a_2994_, v___x_3017_);
v___x_3019_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3018_);
v___x_3020_ = l_Lean_Syntax_node1(v___x_3018_, v___x_3019_, v___x_3016_);
v___x_3021_ = l_Lean_Syntax_node2(v___x_3018_, v___x_2996_, v___x_3015_, v___x_3020_);
v___x_3022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_a_2995_);
return v___x_3022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray___boxed(lean_object* v_x_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_unexpandTSyntaxArray(v_x_3023_, v_a_3024_, v_a_3025_);
lean_dec(v_a_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray(lean_object* v_x_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3030_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3027_);
v___x_3031_ = l_Lean_Syntax_isOfKind(v_x_3027_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v_x_3027_);
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v_a_3029_);
return v___x_3033_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; 
v___x_3034_ = lean_unsigned_to_nat(1u);
v___x_3035_ = l_Lean_Syntax_getArg(v_x_3027_, v___x_3034_);
v___x_3036_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3035_);
v___x_3037_ = l_Lean_Syntax_matchesNull(v___x_3035_, v___x_3036_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec(v___x_3035_);
lean_dec(v_x_3027_);
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_a_3029_);
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v___x_3043_; 
v___x_3040_ = lean_unsigned_to_nat(0u);
v___x_3041_ = l_Lean_Syntax_getArg(v___x_3035_, v___x_3040_);
v___x_3042_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_3041_);
v___x_3043_ = l_Lean_Syntax_isOfKind(v___x_3041_, v___x_3042_);
if (v___x_3043_ == 0)
{
lean_object* v___x_3044_; lean_object* v___x_3045_; 
lean_dec(v___x_3041_);
lean_dec(v___x_3035_);
lean_dec(v_x_3027_);
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3044_);
lean_ctor_set(v___x_3045_, 1, v_a_3029_);
return v___x_3045_;
}
else
{
lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = l_Lean_Syntax_getArg(v___x_3041_, v___x_3034_);
lean_dec(v___x_3041_);
lean_inc(v___x_3046_);
v___x_3047_ = l_Lean_Syntax_matchesNull(v___x_3046_, v___x_3034_);
if (v___x_3047_ == 0)
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
lean_dec(v___x_3046_);
lean_dec(v___x_3035_);
lean_dec(v_x_3027_);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
lean_ctor_set(v___x_3049_, 1, v_a_3029_);
return v___x_3049_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3050_ = l_Lean_Syntax_getArg(v_x_3027_, v___x_3040_);
lean_dec(v_x_3027_);
v___x_3051_ = l_Lean_Syntax_getArg(v___x_3046_, v___x_3040_);
lean_dec(v___x_3046_);
v___x_3052_ = l_Lean_Syntax_getArg(v___x_3035_, v___x_3034_);
lean_dec(v___x_3035_);
v___x_3053_ = 0;
v___x_3054_ = l_Lean_SourceInfo_fromRef(v_a_3028_, v___x_3053_);
v___x_3055_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3054_);
v___x_3056_ = l_Lean_Syntax_node2(v___x_3054_, v___x_3055_, v___x_3051_, v___x_3052_);
v___x_3057_ = l_Lean_Syntax_node2(v___x_3054_, v___x_3030_, v___x_3050_, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_3029_);
return v___x_3058_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray___boxed(lean_object* v_x_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_unexpandTSepArray(v_x_3059_, v_a_3060_, v_a_3061_);
lean_dec(v_a_3060_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem(lean_object* v_x_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v___x_3069_; uint8_t v___x_3070_; 
v___x_3069_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3066_);
v___x_3070_ = l_Lean_Syntax_isOfKind(v_x_3066_, v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec(v_x_3066_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v_a_3068_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v___x_3073_ = lean_unsigned_to_nat(1u);
v___x_3074_ = l_Lean_Syntax_getArg(v_x_3066_, v___x_3073_);
lean_dec(v_x_3066_);
v___x_3075_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3074_);
v___x_3076_ = l_Lean_Syntax_matchesNull(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v_a_3068_);
return v___x_3078_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = l_Lean_Syntax_getArg(v___x_3074_, v___x_3079_);
v___x_3081_ = l_Lean_Syntax_getArg(v___x_3074_, v___x_3073_);
lean_dec(v___x_3074_);
v___x_3082_ = 0;
v___x_3083_ = l_Lean_SourceInfo_fromRef(v_a_3067_, v___x_3082_);
v___x_3084_ = ((lean_object*)(l_unexpandGetElem___closed__1));
v___x_3085_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_3083_, 2);
v___x_3086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3083_);
lean_ctor_set(v___x_3086_, 1, v___x_3085_);
v___x_3087_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3083_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = l_Lean_Syntax_node4(v___x_3083_, v___x_3084_, v___x_3080_, v___x_3086_, v___x_3081_, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
lean_ctor_set(v___x_3090_, 1, v_a_3068_);
return v___x_3090_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem___boxed(lean_object* v_x_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_unexpandGetElem(v_x_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3092_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21(lean_object* v_x_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3102_; uint8_t v___x_3103_; 
v___x_3102_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3099_);
v___x_3103_ = l_Lean_Syntax_isOfKind(v_x_3099_, v___x_3102_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v_x_3099_);
v___x_3104_ = lean_box(0);
v___x_3105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3105_, 0, v___x_3104_);
lean_ctor_set(v___x_3105_, 1, v_a_3101_);
return v___x_3105_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3106_ = lean_unsigned_to_nat(1u);
v___x_3107_ = l_Lean_Syntax_getArg(v_x_3099_, v___x_3106_);
lean_dec(v_x_3099_);
v___x_3108_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3107_);
v___x_3109_ = l_Lean_Syntax_matchesNull(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v_a_3101_);
return v___x_3111_;
}
else
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = l_Lean_Syntax_getArg(v___x_3107_, v___x_3112_);
v___x_3114_ = l_Lean_Syntax_getArg(v___x_3107_, v___x_3106_);
lean_dec(v___x_3107_);
v___x_3115_ = 0;
v___x_3116_ = l_Lean_SourceInfo_fromRef(v_a_3100_, v___x_3115_);
v___x_3117_ = ((lean_object*)(l_unexpandGetElem_x21___closed__1));
v___x_3118_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_3119_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_3116_, 4);
v___x_3120_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3116_);
lean_ctor_set(v___x_3120_, 1, v___x_3118_);
lean_ctor_set(v___x_3120_, 2, v___x_3119_);
v___x_3121_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_3122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3116_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3124_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3116_);
lean_ctor_set(v___x_3124_, 1, v___x_3123_);
v___x_3125_ = ((lean_object*)(l_unexpandGetElem_x21___closed__2));
v___x_3126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3116_);
lean_ctor_set(v___x_3126_, 1, v___x_3125_);
lean_inc_ref(v___x_3120_);
v___x_3127_ = l_Lean_Syntax_node7(v___x_3116_, v___x_3117_, v___x_3113_, v___x_3120_, v___x_3122_, v___x_3114_, v___x_3124_, v___x_3120_, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
lean_ctor_set(v___x_3128_, 1, v_a_3101_);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21___boxed(lean_object* v_x_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l_unexpandGetElem_x21(v_x_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3130_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f(lean_object* v_x_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_){
_start:
{
lean_object* v___x_3140_; uint8_t v___x_3141_; 
v___x_3140_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3137_);
v___x_3141_ = l_Lean_Syntax_isOfKind(v_x_3137_, v___x_3140_);
if (v___x_3141_ == 0)
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_x_3137_);
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v_a_3139_);
return v___x_3143_;
}
else
{
lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v___x_3144_ = lean_unsigned_to_nat(1u);
v___x_3145_ = l_Lean_Syntax_getArg(v_x_3137_, v___x_3144_);
lean_dec(v_x_3137_);
v___x_3146_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3145_);
v___x_3147_ = l_Lean_Syntax_matchesNull(v___x_3145_, v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3148_);
lean_ctor_set(v___x_3149_, 1, v_a_3139_);
return v___x_3149_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = l_Lean_Syntax_getArg(v___x_3145_, v___x_3150_);
v___x_3152_ = l_Lean_Syntax_getArg(v___x_3145_, v___x_3144_);
lean_dec(v___x_3145_);
v___x_3153_ = 0;
v___x_3154_ = l_Lean_SourceInfo_fromRef(v_a_3138_, v___x_3153_);
v___x_3155_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__1));
v___x_3156_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_3157_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_3154_, 4);
v___x_3158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___x_3156_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
v___x_3159_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_3160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3154_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3162_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3154_);
lean_ctor_set(v___x_3162_, 1, v___x_3161_);
v___x_3163_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__2));
v___x_3164_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3154_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
lean_inc_ref(v___x_3158_);
v___x_3165_ = l_Lean_Syntax_node7(v___x_3154_, v___x_3155_, v___x_3151_, v___x_3158_, v___x_3160_, v___x_3152_, v___x_3162_, v___x_3158_, v___x_3164_);
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v_a_3139_);
return v___x_3166_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f___boxed(lean_object* v_x_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_unexpandGetElem_x3f(v_x_3167_, v_a_3168_, v_a_3169_);
lean_dec(v_a_3168_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg(lean_object* v_a_3171_, lean_object* v_a_3172_){
_start:
{
uint8_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3173_ = 0;
v___x_3174_ = l_Lean_SourceInfo_fromRef(v_a_3171_, v___x_3173_);
v___x_3175_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3176_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3174_, 3);
v___x_3177_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3174_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
v___x_3178_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3179_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3174_);
lean_ctor_set(v___x_3180_, 1, v___x_3178_);
lean_ctor_set(v___x_3180_, 2, v___x_3179_);
v___x_3181_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3174_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = l_Lean_Syntax_node3(v___x_3174_, v___x_3175_, v___x_3177_, v___x_3180_, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3183_);
lean_ctor_set(v___x_3184_, 1, v_a_3172_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg___boxed(lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_unexpandArrayEmpty___redArg(v_a_3185_, v_a_3186_);
lean_dec(v_a_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty(lean_object* v_x_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_unexpandArrayEmpty___redArg(v_a_3189_, v_a_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___boxed(lean_object* v_x_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_unexpandArrayEmpty(v_x_3192_, v_a_3193_, v_a_3194_);
lean_dec(v_a_3193_);
lean_dec(v_x_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg(lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
uint8_t v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3198_ = 0;
v___x_3199_ = l_Lean_SourceInfo_fromRef(v_a_3196_, v___x_3198_);
v___x_3200_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3201_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3199_, 3);
v___x_3202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3202_, 0, v___x_3199_);
lean_ctor_set(v___x_3202_, 1, v___x_3201_);
v___x_3203_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3204_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3205_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3199_);
lean_ctor_set(v___x_3205_, 1, v___x_3203_);
lean_ctor_set(v___x_3205_, 2, v___x_3204_);
v___x_3206_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3199_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = l_Lean_Syntax_node3(v___x_3199_, v___x_3200_, v___x_3202_, v___x_3205_, v___x_3207_);
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
lean_ctor_set(v___x_3209_, 1, v_a_3197_);
return v___x_3209_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg___boxed(lean_object* v_a_3210_, lean_object* v_a_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_unexpandMkArray0___redArg(v_a_3210_, v_a_3211_);
lean_dec(v_a_3210_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0(lean_object* v_x_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_unexpandMkArray0___redArg(v_a_3214_, v_a_3215_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___boxed(lean_object* v_x_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_unexpandMkArray0(v_x_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3218_);
lean_dec(v_x_3217_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1(lean_object* v_x_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3224_; uint8_t v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3221_);
v___x_3225_ = l_Lean_Syntax_isOfKind(v_x_3221_, v___x_3224_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec(v_x_3221_);
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v_a_3223_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3228_ = lean_unsigned_to_nat(1u);
v___x_3229_ = l_Lean_Syntax_getArg(v_x_3221_, v___x_3228_);
lean_dec(v_x_3221_);
lean_inc(v___x_3229_);
v___x_3230_ = l_Lean_Syntax_matchesNull(v___x_3229_, v___x_3228_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v___x_3229_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_a_3223_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3233_ = lean_unsigned_to_nat(0u);
v___x_3234_ = l_Lean_Syntax_getArg(v___x_3229_, v___x_3233_);
lean_dec(v___x_3229_);
v___x_3235_ = 0;
v___x_3236_ = l_Lean_SourceInfo_fromRef(v_a_3222_, v___x_3235_);
v___x_3237_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3238_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3236_, 3);
v___x_3239_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3236_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3241_ = l_Lean_Syntax_node1(v___x_3236_, v___x_3240_, v___x_3234_);
v___x_3242_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3236_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_Syntax_node3(v___x_3236_, v___x_3237_, v___x_3239_, v___x_3241_, v___x_3243_);
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
lean_ctor_set(v___x_3245_, 1, v_a_3223_);
return v___x_3245_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1___boxed(lean_object* v_x_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_){
_start:
{
lean_object* v_res_3249_; 
v_res_3249_ = l_unexpandMkArray1(v_x_3246_, v_a_3247_, v_a_3248_);
lean_dec(v_a_3247_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2(lean_object* v_x_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3250_);
v___x_3254_ = l_Lean_Syntax_isOfKind(v_x_3250_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec(v_x_3250_);
v___x_3255_ = lean_box(0);
v___x_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v_a_3252_);
return v___x_3256_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3257_ = lean_unsigned_to_nat(1u);
v___x_3258_ = l_Lean_Syntax_getArg(v_x_3250_, v___x_3257_);
lean_dec(v_x_3250_);
v___x_3259_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3258_);
v___x_3260_ = l_Lean_Syntax_matchesNull(v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_a_3252_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3263_ = lean_unsigned_to_nat(0u);
v___x_3264_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3263_);
v___x_3265_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3257_);
lean_dec(v___x_3258_);
v___x_3266_ = 0;
v___x_3267_ = l_Lean_SourceInfo_fromRef(v_a_3251_, v___x_3266_);
v___x_3268_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3269_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3267_, 4);
v___x_3270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3267_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3272_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3267_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_Syntax_node3(v___x_3267_, v___x_3271_, v___x_3264_, v___x_3273_, v___x_3265_);
v___x_3275_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3276_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3267_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_Syntax_node3(v___x_3267_, v___x_3268_, v___x_3270_, v___x_3274_, v___x_3276_);
v___x_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
lean_ctor_set(v___x_3278_, 1, v_a_3252_);
return v___x_3278_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2___boxed(lean_object* v_x_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l_unexpandMkArray2(v_x_3279_, v_a_3280_, v_a_3281_);
lean_dec(v_a_3280_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3(lean_object* v_x_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3286_; uint8_t v___x_3287_; 
v___x_3286_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3283_);
v___x_3287_ = l_Lean_Syntax_isOfKind(v_x_3283_, v___x_3286_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
lean_dec(v_x_3283_);
v___x_3288_ = lean_box(0);
v___x_3289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v_a_3285_);
return v___x_3289_;
}
else
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; uint8_t v___x_3293_; 
v___x_3290_ = lean_unsigned_to_nat(1u);
v___x_3291_ = l_Lean_Syntax_getArg(v_x_3283_, v___x_3290_);
lean_dec(v_x_3283_);
v___x_3292_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3291_);
v___x_3293_ = l_Lean_Syntax_matchesNull(v___x_3291_, v___x_3292_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
lean_dec(v___x_3291_);
v___x_3294_ = lean_box(0);
v___x_3295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3294_);
lean_ctor_set(v___x_3295_, 1, v_a_3285_);
return v___x_3295_;
}
else
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = l_Lean_Syntax_getArg(v___x_3291_, v___x_3296_);
v___x_3298_ = l_Lean_Syntax_getArg(v___x_3291_, v___x_3290_);
v___x_3299_ = lean_unsigned_to_nat(2u);
v___x_3300_ = l_Lean_Syntax_getArg(v___x_3291_, v___x_3299_);
lean_dec(v___x_3291_);
v___x_3301_ = 0;
v___x_3302_ = l_Lean_SourceInfo_fromRef(v_a_3284_, v___x_3301_);
v___x_3303_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3304_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3302_, 4);
v___x_3305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3302_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3307_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3302_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_inc_ref(v___x_3308_);
v___x_3309_ = l_Lean_Syntax_node5(v___x_3302_, v___x_3306_, v___x_3297_, v___x_3308_, v___x_3298_, v___x_3308_, v___x_3300_);
v___x_3310_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3311_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3302_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_Syntax_node3(v___x_3302_, v___x_3303_, v___x_3305_, v___x_3309_, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v_a_3285_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3___boxed(lean_object* v_x_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_unexpandMkArray3(v_x_3314_, v_a_3315_, v_a_3316_);
lean_dec(v_a_3315_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4(lean_object* v_x_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3318_);
v___x_3322_ = l_Lean_Syntax_isOfKind(v_x_3318_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec(v_x_3318_);
v___x_3323_ = lean_box(0);
v___x_3324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v_a_3320_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3325_ = lean_unsigned_to_nat(1u);
v___x_3326_ = l_Lean_Syntax_getArg(v_x_3318_, v___x_3325_);
lean_dec(v_x_3318_);
v___x_3327_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_3326_);
v___x_3328_ = l_Lean_Syntax_matchesNull(v___x_3326_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_dec(v___x_3326_);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v_a_3320_);
return v___x_3330_;
}
else
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3331_ = lean_unsigned_to_nat(0u);
v___x_3332_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3331_);
v___x_3333_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3325_);
v___x_3334_ = lean_unsigned_to_nat(2u);
v___x_3335_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3334_);
v___x_3336_ = lean_unsigned_to_nat(3u);
v___x_3337_ = l_Lean_Syntax_getArg(v___x_3326_, v___x_3336_);
lean_dec(v___x_3326_);
v___x_3338_ = 0;
v___x_3339_ = l_Lean_SourceInfo_fromRef(v_a_3319_, v___x_3338_);
v___x_3340_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3341_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3339_, 4);
v___x_3342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3339_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3344_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3339_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
lean_inc_ref_n(v___x_3345_, 2);
v___x_3346_ = l_Lean_Syntax_node7(v___x_3339_, v___x_3343_, v___x_3332_, v___x_3345_, v___x_3333_, v___x_3345_, v___x_3335_, v___x_3345_, v___x_3337_);
v___x_3347_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3339_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = l_Lean_Syntax_node3(v___x_3339_, v___x_3340_, v___x_3342_, v___x_3346_, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v_a_3320_);
return v___x_3350_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4___boxed(lean_object* v_x_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_unexpandMkArray4(v_x_3351_, v_a_3352_, v_a_3353_);
lean_dec(v_a_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5(lean_object* v_x_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_){
_start:
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3355_);
v___x_3359_ = l_Lean_Syntax_isOfKind(v_x_3355_, v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec(v_x_3355_);
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v_a_3357_);
return v___x_3361_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v___x_3362_ = lean_unsigned_to_nat(1u);
v___x_3363_ = l_Lean_Syntax_getArg(v_x_3355_, v___x_3362_);
lean_dec(v_x_3355_);
v___x_3364_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3363_);
v___x_3365_ = l_Lean_Syntax_matchesNull(v___x_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v___x_3367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3366_);
lean_ctor_set(v___x_3367_, 1, v_a_3357_);
return v___x_3367_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = l_Lean_Syntax_getArg(v___x_3363_, v___x_3368_);
v___x_3370_ = l_Lean_Syntax_getArg(v___x_3363_, v___x_3362_);
v___x_3371_ = lean_unsigned_to_nat(2u);
v___x_3372_ = l_Lean_Syntax_getArg(v___x_3363_, v___x_3371_);
v___x_3373_ = lean_unsigned_to_nat(3u);
v___x_3374_ = l_Lean_Syntax_getArg(v___x_3363_, v___x_3373_);
v___x_3375_ = lean_unsigned_to_nat(4u);
v___x_3376_ = l_Lean_Syntax_getArg(v___x_3363_, v___x_3375_);
lean_dec(v___x_3363_);
v___x_3377_ = 0;
v___x_3378_ = l_Lean_SourceInfo_fromRef(v_a_3356_, v___x_3377_);
v___x_3379_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3380_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3378_, 4);
v___x_3381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3378_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3383_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3384_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3378_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = lean_unsigned_to_nat(9u);
v___x_3386_ = lean_mk_empty_array_with_capacity(v___x_3385_);
v___x_3387_ = lean_array_push(v___x_3386_, v___x_3369_);
lean_inc_ref_n(v___x_3384_, 3);
v___x_3388_ = lean_array_push(v___x_3387_, v___x_3384_);
v___x_3389_ = lean_array_push(v___x_3388_, v___x_3370_);
v___x_3390_ = lean_array_push(v___x_3389_, v___x_3384_);
v___x_3391_ = lean_array_push(v___x_3390_, v___x_3372_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3384_);
v___x_3393_ = lean_array_push(v___x_3392_, v___x_3374_);
v___x_3394_ = lean_array_push(v___x_3393_, v___x_3384_);
v___x_3395_ = lean_array_push(v___x_3394_, v___x_3376_);
v___x_3396_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3378_);
lean_ctor_set(v___x_3396_, 1, v___x_3382_);
lean_ctor_set(v___x_3396_, 2, v___x_3395_);
v___x_3397_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3378_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = l_Lean_Syntax_node3(v___x_3378_, v___x_3379_, v___x_3381_, v___x_3396_, v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
lean_ctor_set(v___x_3400_, 1, v_a_3357_);
return v___x_3400_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5___boxed(lean_object* v_x_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_unexpandMkArray5(v_x_3401_, v_a_3402_, v_a_3403_);
lean_dec(v_a_3402_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6(lean_object* v_x_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3408_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3405_);
v___x_3409_ = l_Lean_Syntax_isOfKind(v_x_3405_, v___x_3408_);
if (v___x_3409_ == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec(v_x_3405_);
v___x_3410_ = lean_box(0);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3410_);
lean_ctor_set(v___x_3411_, 1, v_a_3407_);
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = l_Lean_Syntax_getArg(v_x_3405_, v___x_3412_);
lean_dec(v_x_3405_);
v___x_3414_ = lean_unsigned_to_nat(6u);
lean_inc(v___x_3413_);
v___x_3415_ = l_Lean_Syntax_matchesNull(v___x_3413_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec(v___x_3413_);
v___x_3416_ = lean_box(0);
v___x_3417_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v_a_3407_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; 
v___x_3418_ = lean_unsigned_to_nat(0u);
v___x_3419_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3418_);
v___x_3420_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3412_);
v___x_3421_ = lean_unsigned_to_nat(2u);
v___x_3422_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3421_);
v___x_3423_ = lean_unsigned_to_nat(3u);
v___x_3424_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3423_);
v___x_3425_ = lean_unsigned_to_nat(4u);
v___x_3426_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3425_);
v___x_3427_ = lean_unsigned_to_nat(5u);
v___x_3428_ = l_Lean_Syntax_getArg(v___x_3413_, v___x_3427_);
lean_dec(v___x_3413_);
v___x_3429_ = 0;
v___x_3430_ = l_Lean_SourceInfo_fromRef(v_a_3406_, v___x_3429_);
v___x_3431_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3432_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3430_, 4);
v___x_3433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3430_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3435_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3436_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3430_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = lean_unsigned_to_nat(11u);
v___x_3438_ = lean_mk_empty_array_with_capacity(v___x_3437_);
v___x_3439_ = lean_array_push(v___x_3438_, v___x_3419_);
lean_inc_ref_n(v___x_3436_, 4);
v___x_3440_ = lean_array_push(v___x_3439_, v___x_3436_);
v___x_3441_ = lean_array_push(v___x_3440_, v___x_3420_);
v___x_3442_ = lean_array_push(v___x_3441_, v___x_3436_);
v___x_3443_ = lean_array_push(v___x_3442_, v___x_3422_);
v___x_3444_ = lean_array_push(v___x_3443_, v___x_3436_);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3424_);
v___x_3446_ = lean_array_push(v___x_3445_, v___x_3436_);
v___x_3447_ = lean_array_push(v___x_3446_, v___x_3426_);
v___x_3448_ = lean_array_push(v___x_3447_, v___x_3436_);
v___x_3449_ = lean_array_push(v___x_3448_, v___x_3428_);
v___x_3450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3430_);
lean_ctor_set(v___x_3450_, 1, v___x_3434_);
lean_ctor_set(v___x_3450_, 2, v___x_3449_);
v___x_3451_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3430_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l_Lean_Syntax_node3(v___x_3430_, v___x_3431_, v___x_3433_, v___x_3450_, v___x_3452_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3453_);
lean_ctor_set(v___x_3454_, 1, v_a_3407_);
return v___x_3454_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6___boxed(lean_object* v_x_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_unexpandMkArray6(v_x_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3456_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7(lean_object* v_x_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3459_);
v___x_3463_ = l_Lean_Syntax_isOfKind(v_x_3459_, v___x_3462_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec(v_x_3459_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v_a_3461_);
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; uint8_t v___x_3469_; 
v___x_3466_ = lean_unsigned_to_nat(1u);
v___x_3467_ = l_Lean_Syntax_getArg(v_x_3459_, v___x_3466_);
lean_dec(v_x_3459_);
v___x_3468_ = lean_unsigned_to_nat(7u);
lean_inc(v___x_3467_);
v___x_3469_ = l_Lean_Syntax_matchesNull(v___x_3467_, v___x_3468_);
if (v___x_3469_ == 0)
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v___x_3467_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
lean_ctor_set(v___x_3471_, 1, v_a_3461_);
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3472_);
v___x_3474_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3466_);
v___x_3475_ = lean_unsigned_to_nat(2u);
v___x_3476_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3475_);
v___x_3477_ = lean_unsigned_to_nat(3u);
v___x_3478_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3477_);
v___x_3479_ = lean_unsigned_to_nat(4u);
v___x_3480_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3479_);
v___x_3481_ = lean_unsigned_to_nat(5u);
v___x_3482_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3481_);
v___x_3483_ = lean_unsigned_to_nat(6u);
v___x_3484_ = l_Lean_Syntax_getArg(v___x_3467_, v___x_3483_);
lean_dec(v___x_3467_);
v___x_3485_ = 0;
v___x_3486_ = l_Lean_SourceInfo_fromRef(v_a_3460_, v___x_3485_);
v___x_3487_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3488_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3486_, 4);
v___x_3489_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3486_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3491_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3492_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3486_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = lean_unsigned_to_nat(13u);
v___x_3494_ = lean_mk_empty_array_with_capacity(v___x_3493_);
v___x_3495_ = lean_array_push(v___x_3494_, v___x_3473_);
lean_inc_ref_n(v___x_3492_, 5);
v___x_3496_ = lean_array_push(v___x_3495_, v___x_3492_);
v___x_3497_ = lean_array_push(v___x_3496_, v___x_3474_);
v___x_3498_ = lean_array_push(v___x_3497_, v___x_3492_);
v___x_3499_ = lean_array_push(v___x_3498_, v___x_3476_);
v___x_3500_ = lean_array_push(v___x_3499_, v___x_3492_);
v___x_3501_ = lean_array_push(v___x_3500_, v___x_3478_);
v___x_3502_ = lean_array_push(v___x_3501_, v___x_3492_);
v___x_3503_ = lean_array_push(v___x_3502_, v___x_3480_);
v___x_3504_ = lean_array_push(v___x_3503_, v___x_3492_);
v___x_3505_ = lean_array_push(v___x_3504_, v___x_3482_);
v___x_3506_ = lean_array_push(v___x_3505_, v___x_3492_);
v___x_3507_ = lean_array_push(v___x_3506_, v___x_3484_);
v___x_3508_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3486_);
lean_ctor_set(v___x_3508_, 1, v___x_3490_);
lean_ctor_set(v___x_3508_, 2, v___x_3507_);
v___x_3509_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3510_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3486_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = l_Lean_Syntax_node3(v___x_3486_, v___x_3487_, v___x_3489_, v___x_3508_, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
lean_ctor_set(v___x_3512_, 1, v_a_3461_);
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7___boxed(lean_object* v_x_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_unexpandMkArray7(v_x_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8(lean_object* v_x_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3520_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3517_);
v___x_3521_ = l_Lean_Syntax_isOfKind(v_x_3517_, v___x_3520_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec(v_x_3517_);
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
lean_ctor_set(v___x_3523_, 1, v_a_3519_);
return v___x_3523_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3524_ = lean_unsigned_to_nat(1u);
v___x_3525_ = l_Lean_Syntax_getArg(v_x_3517_, v___x_3524_);
lean_dec(v_x_3517_);
v___x_3526_ = lean_unsigned_to_nat(8u);
lean_inc(v___x_3525_);
v___x_3527_ = l_Lean_Syntax_matchesNull(v___x_3525_, v___x_3526_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v___x_3529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v_a_3519_);
return v___x_3529_;
}
else
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3530_ = lean_unsigned_to_nat(0u);
v___x_3531_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3530_);
v___x_3532_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3524_);
v___x_3533_ = lean_unsigned_to_nat(2u);
v___x_3534_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3533_);
v___x_3535_ = lean_unsigned_to_nat(3u);
v___x_3536_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3535_);
v___x_3537_ = lean_unsigned_to_nat(4u);
v___x_3538_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3537_);
v___x_3539_ = lean_unsigned_to_nat(5u);
v___x_3540_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3539_);
v___x_3541_ = lean_unsigned_to_nat(6u);
v___x_3542_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3541_);
v___x_3543_ = lean_unsigned_to_nat(7u);
v___x_3544_ = l_Lean_Syntax_getArg(v___x_3525_, v___x_3543_);
lean_dec(v___x_3525_);
v___x_3545_ = 0;
v___x_3546_ = l_Lean_SourceInfo_fromRef(v_a_3518_, v___x_3545_);
v___x_3547_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3548_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3546_, 4);
v___x_3549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3546_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3551_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3546_);
lean_ctor_set(v___x_3552_, 1, v___x_3551_);
v___x_3553_ = lean_unsigned_to_nat(15u);
v___x_3554_ = lean_mk_empty_array_with_capacity(v___x_3553_);
v___x_3555_ = lean_array_push(v___x_3554_, v___x_3531_);
lean_inc_ref_n(v___x_3552_, 6);
v___x_3556_ = lean_array_push(v___x_3555_, v___x_3552_);
v___x_3557_ = lean_array_push(v___x_3556_, v___x_3532_);
v___x_3558_ = lean_array_push(v___x_3557_, v___x_3552_);
v___x_3559_ = lean_array_push(v___x_3558_, v___x_3534_);
v___x_3560_ = lean_array_push(v___x_3559_, v___x_3552_);
v___x_3561_ = lean_array_push(v___x_3560_, v___x_3536_);
v___x_3562_ = lean_array_push(v___x_3561_, v___x_3552_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3538_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3552_);
v___x_3565_ = lean_array_push(v___x_3564_, v___x_3540_);
v___x_3566_ = lean_array_push(v___x_3565_, v___x_3552_);
v___x_3567_ = lean_array_push(v___x_3566_, v___x_3542_);
v___x_3568_ = lean_array_push(v___x_3567_, v___x_3552_);
v___x_3569_ = lean_array_push(v___x_3568_, v___x_3544_);
v___x_3570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3570_, 0, v___x_3546_);
lean_ctor_set(v___x_3570_, 1, v___x_3550_);
lean_ctor_set(v___x_3570_, 2, v___x_3569_);
v___x_3571_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3546_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_Syntax_node3(v___x_3546_, v___x_3547_, v___x_3549_, v___x_3570_, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v_a_3519_);
return v___x_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8___boxed(lean_object* v_x_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_unexpandMkArray8(v_x_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3576_);
return v_res_3578_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3627_ = l_String_toRawSubstring_x27(v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1(lean_object* v_x_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3659_ = ((lean_object*)(l_tacticFunext_______00__closed__1));
lean_inc(v_x_3656_);
v___x_3660_ = l_Lean_Syntax_isOfKind(v_x_3656_, v___x_3659_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_dec(v_x_3656_);
v___x_3661_ = lean_box(1);
v___x_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
lean_ctor_set(v___x_3662_, 1, v_a_3658_);
return v___x_3662_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3663_ = lean_unsigned_to_nat(0u);
v___x_3664_ = lean_unsigned_to_nat(1u);
v___x_3665_ = l_Lean_Syntax_getArg(v_x_3656_, v___x_3664_);
lean_dec(v_x_3656_);
lean_inc(v___x_3665_);
v___x_3666_ = l_Lean_Syntax_matchesNull(v___x_3665_, v___x_3663_);
if (v___x_3666_ == 0)
{
uint8_t v___x_3667_; 
lean_inc(v___x_3665_);
v___x_3667_ = l_Lean_Syntax_matchesNull(v___x_3665_, v___x_3664_);
if (v___x_3667_ == 0)
{
lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3668_ = l_Lean_Syntax_getNumArgs(v___x_3665_);
v___x_3669_ = lean_nat_dec_le(v___x_3664_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec(v___x_3668_);
lean_dec(v___x_3665_);
v___x_3670_ = lean_box(1);
v___x_3671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v_a_3658_);
return v___x_3671_;
}
else
{
lean_object* v_quotContext_3672_; lean_object* v_currMacroScope_3673_; lean_object* v_ref_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_xs_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_quotContext_3672_ = lean_ctor_get(v_a_3657_, 1);
v_currMacroScope_3673_ = lean_ctor_get(v_a_3657_, 2);
v_ref_3674_ = lean_ctor_get(v_a_3657_, 5);
v___x_3675_ = l_Lean_Syntax_getArg(v___x_3665_, v___x_3663_);
v___x_3676_ = l_Lean_Syntax_getArgs(v___x_3665_);
lean_dec(v___x_3665_);
v___x_3677_ = l_Array_extract___redArg(v___x_3676_, v___x_3664_, v___x_3668_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3679_ = lean_box(2);
v___x_3680_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
lean_ctor_set(v___x_3680_, 1, v___x_3678_);
lean_ctor_set(v___x_3680_, 2, v___x_3677_);
v_xs_3681_ = l_Lean_Syntax_getArgs(v___x_3680_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = l_Lean_SourceInfo_fromRef(v_ref_3674_, v___x_3667_);
v___x_3683_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3684_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3685_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3682_, 11);
v___x_3686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3682_);
lean_ctor_set(v___x_3686_, 1, v___x_3684_);
v___x_3687_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3688_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3689_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3673_);
lean_inc(v_quotContext_3672_);
v___x_3690_ = l_Lean_addMacroScope(v_quotContext_3672_, v___x_3689_, v_currMacroScope_3673_);
v___x_3691_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3692_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3682_);
lean_ctor_set(v___x_3692_, 1, v___x_3688_);
lean_ctor_set(v___x_3692_, 2, v___x_3690_);
lean_ctor_set(v___x_3692_, 3, v___x_3691_);
v___x_3693_ = l_Lean_Syntax_node2(v___x_3682_, v___x_3685_, v___x_3686_, v___x_3692_);
v___x_3694_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3682_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3697_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3698_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3682_);
lean_ctor_set(v___x_3698_, 1, v___x_3696_);
v___x_3699_ = l_Lean_Syntax_node1(v___x_3682_, v___x_3678_, v___x_3675_);
v___x_3700_ = l_Lean_Syntax_node2(v___x_3682_, v___x_3697_, v___x_3698_, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3682_);
lean_ctor_set(v___x_3701_, 1, v___x_3687_);
v___x_3702_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3703_ = l_Array_append___redArg(v___x_3702_, v_xs_3681_);
lean_dec_ref(v_xs_3681_);
v___x_3704_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3682_);
lean_ctor_set(v___x_3704_, 1, v___x_3678_);
lean_ctor_set(v___x_3704_, 2, v___x_3703_);
v___x_3705_ = l_Lean_Syntax_node2(v___x_3682_, v___x_3659_, v___x_3701_, v___x_3704_);
lean_inc_ref(v___x_3695_);
v___x_3706_ = l_Lean_Syntax_node5(v___x_3682_, v___x_3678_, v___x_3693_, v___x_3695_, v___x_3700_, v___x_3695_, v___x_3705_);
v___x_3707_ = l_Lean_Syntax_node1(v___x_3682_, v___x_3683_, v___x_3706_);
v___x_3708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v_a_3658_);
return v___x_3708_;
}
}
else
{
lean_object* v_quotContext_3709_; lean_object* v_currMacroScope_3710_; lean_object* v_ref_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_quotContext_3709_ = lean_ctor_get(v_a_3657_, 1);
v_currMacroScope_3710_ = lean_ctor_get(v_a_3657_, 2);
v_ref_3711_ = lean_ctor_get(v_a_3657_, 5);
v___x_3712_ = l_Lean_Syntax_getArg(v___x_3665_, v___x_3663_);
lean_dec(v___x_3665_);
v___x_3713_ = l_Lean_SourceInfo_fromRef(v_ref_3711_, v___x_3666_);
v___x_3714_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3715_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3716_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3717_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3713_, 8);
v___x_3718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3713_);
lean_ctor_set(v___x_3718_, 1, v___x_3716_);
v___x_3719_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3720_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3710_);
lean_inc(v_quotContext_3709_);
v___x_3721_ = l_Lean_addMacroScope(v_quotContext_3709_, v___x_3720_, v_currMacroScope_3710_);
v___x_3722_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3723_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3713_);
lean_ctor_set(v___x_3723_, 1, v___x_3719_);
lean_ctor_set(v___x_3723_, 2, v___x_3721_);
lean_ctor_set(v___x_3723_, 3, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node2(v___x_3713_, v___x_3717_, v___x_3718_, v___x_3723_);
v___x_3725_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3713_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3728_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3729_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3713_);
lean_ctor_set(v___x_3729_, 1, v___x_3727_);
v___x_3730_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3715_, v___x_3712_);
v___x_3731_ = l_Lean_Syntax_node2(v___x_3713_, v___x_3728_, v___x_3729_, v___x_3730_);
v___x_3732_ = l_Lean_Syntax_node3(v___x_3713_, v___x_3715_, v___x_3724_, v___x_3726_, v___x_3731_);
v___x_3733_ = l_Lean_Syntax_node1(v___x_3713_, v___x_3714_, v___x_3732_);
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3733_);
lean_ctor_set(v___x_3734_, 1, v_a_3658_);
return v___x_3734_;
}
}
else
{
lean_object* v_quotContext_3735_; lean_object* v_currMacroScope_3736_; lean_object* v_ref_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_dec(v___x_3665_);
v_quotContext_3735_ = lean_ctor_get(v_a_3657_, 1);
v_currMacroScope_3736_ = lean_ctor_get(v_a_3657_, 2);
v_ref_3737_ = lean_ctor_get(v_a_3657_, 5);
v___x_3738_ = 0;
v___x_3739_ = l_Lean_SourceInfo_fromRef(v_ref_3737_, v___x_3738_);
v___x_3740_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12));
v___x_3741_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13));
lean_inc_n(v___x_3739_, 17);
v___x_3742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3739_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___x_3743_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_3744_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_3745_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3746_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_3747_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_3748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3739_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3750_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
v___x_3751_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3739_);
lean_ctor_set(v___x_3751_, 1, v___x_3749_);
v___x_3752_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3753_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3736_);
lean_inc(v_quotContext_3735_);
v___x_3754_ = l_Lean_addMacroScope(v_quotContext_3735_, v___x_3753_, v_currMacroScope_3736_);
v___x_3755_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3756_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3739_);
lean_ctor_set(v___x_3756_, 1, v___x_3752_);
lean_ctor_set(v___x_3756_, 2, v___x_3754_);
lean_ctor_set(v___x_3756_, 3, v___x_3755_);
v___x_3757_ = l_Lean_Syntax_node2(v___x_3739_, v___x_3750_, v___x_3751_, v___x_3756_);
v___x_3758_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3739_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3761_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3739_);
lean_ctor_set(v___x_3762_, 1, v___x_3760_);
v___x_3763_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3764_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3739_);
lean_ctor_set(v___x_3764_, 1, v___x_3745_);
lean_ctor_set(v___x_3764_, 2, v___x_3763_);
v___x_3765_ = l_Lean_Syntax_node2(v___x_3739_, v___x_3761_, v___x_3762_, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node3(v___x_3739_, v___x_3745_, v___x_3757_, v___x_3759_, v___x_3765_);
v___x_3767_ = l_Lean_Syntax_node1(v___x_3739_, v___x_3744_, v___x_3766_);
v___x_3768_ = l_Lean_Syntax_node1(v___x_3739_, v___x_3743_, v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_3770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3739_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = l_Lean_Syntax_node3(v___x_3739_, v___x_3746_, v___x_3748_, v___x_3768_, v___x_3770_);
v___x_3772_ = l_Lean_Syntax_node1(v___x_3739_, v___x_3745_, v___x_3771_);
v___x_3773_ = l_Lean_Syntax_node1(v___x_3739_, v___x_3744_, v___x_3772_);
v___x_3774_ = l_Lean_Syntax_node1(v___x_3739_, v___x_3743_, v___x_3773_);
v___x_3775_ = l_Lean_Syntax_node2(v___x_3739_, v___x_3740_, v___x_3742_, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3775_);
lean_ctor_set(v___x_3776_, 1, v_a_3658_);
return v___x_3776_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___boxed(lean_object* v_x_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_){
_start:
{
lean_object* v_res_3780_; 
v_res_3780_ = l___aux__Init__NotationExtra______macroRules__tacticFunext________1(v_x_3777_, v_a_3778_, v_a_3779_);
lean_dec_ref(v_a_3778_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(size_t v_sz_3781_, size_t v_i_3782_, lean_object* v_bs_3783_){
_start:
{
uint8_t v___x_3784_; 
v___x_3784_ = lean_usize_dec_lt(v_i_3782_, v_sz_3781_);
if (v___x_3784_ == 0)
{
return v_bs_3783_;
}
else
{
lean_object* v_v_3785_; lean_object* v___x_3786_; lean_object* v_bs_x27_3787_; size_t v___x_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v_v_3785_ = lean_array_uget(v_bs_3783_, v_i_3782_);
v___x_3786_ = lean_unsigned_to_nat(0u);
v_bs_x27_3787_ = lean_array_uset(v_bs_3783_, v_i_3782_, v___x_3786_);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3782_, v___x_3788_);
v___x_3790_ = lean_array_uset(v_bs_x27_3787_, v_i_3782_, v_v_3785_);
v_i_3782_ = v___x_3789_;
v_bs_3783_ = v___x_3790_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1___boxed(lean_object* v_sz_3792_, lean_object* v_i_3793_, lean_object* v_bs_3794_){
_start:
{
size_t v_sz_boxed_3795_; size_t v_i_boxed_3796_; lean_object* v_res_3797_; 
v_sz_boxed_3795_ = lean_unbox_usize(v_sz_3792_);
lean_dec(v_sz_3792_);
v_i_boxed_3796_ = lean_unbox_usize(v_i_3793_);
lean_dec(v_i_3793_);
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_boxed_3795_, v_i_boxed_3796_, v_bs_3794_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(size_t v_sz_3798_, size_t v_i_3799_, lean_object* v_bs_3800_){
_start:
{
uint8_t v___x_3801_; 
v___x_3801_ = lean_usize_dec_lt(v_i_3799_, v_sz_3798_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3802_, 0, v_bs_3800_);
return v___x_3802_;
}
else
{
lean_object* v_v_3803_; lean_object* v___x_3804_; lean_object* v_bs_x27_3805_; size_t v___x_3806_; size_t v___x_3807_; lean_object* v___x_3808_; 
v_v_3803_ = lean_array_uget(v_bs_3800_, v_i_3799_);
v___x_3804_ = lean_unsigned_to_nat(0u);
v_bs_x27_3805_ = lean_array_uset(v_bs_3800_, v_i_3799_, v___x_3804_);
v___x_3806_ = ((size_t)1ULL);
v___x_3807_ = lean_usize_add(v_i_3799_, v___x_3806_);
v___x_3808_ = lean_array_uset(v_bs_x27_3805_, v_i_3799_, v_v_3803_);
v_i_3799_ = v___x_3807_;
v_bs_3800_ = v___x_3808_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0___boxed(lean_object* v_sz_3810_, lean_object* v_i_3811_, lean_object* v_bs_3812_){
_start:
{
size_t v_sz_boxed_3813_; size_t v_i_boxed_3814_; lean_object* v_res_3815_; 
v_sz_boxed_3813_ = lean_unbox_usize(v_sz_3810_);
lean_dec(v_sz_3810_);
v_i_boxed_3814_ = lean_unbox_usize(v_i_3811_);
lean_dec(v_i_3811_);
v_res_3815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_boxed_3813_, v_i_boxed_3814_, v_bs_3812_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(uint8_t v___x_3816_, lean_object* v_as_3817_, size_t v_i_3818_, size_t v_stop_3819_, lean_object* v_b_3820_){
_start:
{
lean_object* v___y_3822_; uint8_t v___x_3826_; 
v___x_3826_ = lean_usize_dec_eq(v_i_3818_, v_stop_3819_);
if (v___x_3826_ == 0)
{
lean_object* v_fst_3827_; uint8_t v___x_3828_; 
v_fst_3827_ = lean_ctor_get(v_b_3820_, 0);
v___x_3828_ = lean_unbox(v_fst_3827_);
if (v___x_3828_ == 0)
{
lean_object* v_snd_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3837_; 
v_snd_3829_ = lean_ctor_get(v_b_3820_, 1);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_b_3820_);
if (v_isSharedCheck_3837_ == 0)
{
lean_object* v_unused_3838_; 
v_unused_3838_ = lean_ctor_get(v_b_3820_, 0);
lean_dec(v_unused_3838_);
v___x_3831_ = v_b_3820_;
v_isShared_3832_ = v_isSharedCheck_3837_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_snd_3829_);
lean_dec(v_b_3820_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3837_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3833_; lean_object* v___x_3835_; 
v___x_3833_ = lean_box(v___x_3816_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set(v___x_3831_, 0, v___x_3833_);
v___x_3835_ = v___x_3831_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
lean_ctor_set(v_reuseFailAlloc_3836_, 1, v_snd_3829_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
v___y_3822_ = v___x_3835_;
goto v___jp_3821_;
}
}
}
else
{
lean_object* v_snd_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3849_; 
v_snd_3839_ = lean_ctor_get(v_b_3820_, 1);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_b_3820_);
if (v_isSharedCheck_3849_ == 0)
{
lean_object* v_unused_3850_; 
v_unused_3850_ = lean_ctor_get(v_b_3820_, 0);
lean_dec(v_unused_3850_);
v___x_3841_ = v_b_3820_;
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_snd_3839_);
lean_dec(v_b_3820_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3849_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3843_ = lean_array_uget_borrowed(v_as_3817_, v_i_3818_);
lean_inc(v___x_3843_);
v___x_3844_ = lean_array_push(v_snd_3839_, v___x_3843_);
v___x_3845_ = lean_box(v___x_3826_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 1, v___x_3844_);
lean_ctor_set(v___x_3841_, 0, v___x_3845_);
v___x_3847_ = v___x_3841_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___x_3844_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
v___y_3822_ = v___x_3847_;
goto v___jp_3821_;
}
}
}
}
else
{
return v_b_3820_;
}
v___jp_3821_:
{
size_t v___x_3823_; size_t v___x_3824_; 
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3818_, v___x_3823_);
v_i_3818_ = v___x_3824_;
v_b_3820_ = v___y_3822_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3___boxed(lean_object* v___x_3851_, lean_object* v_as_3852_, lean_object* v_i_3853_, lean_object* v_stop_3854_, lean_object* v_b_3855_){
_start:
{
uint8_t v___x_5643__boxed_3856_; size_t v_i_boxed_3857_; size_t v_stop_boxed_3858_; lean_object* v_res_3859_; 
v___x_5643__boxed_3856_ = lean_unbox(v___x_3851_);
v_i_boxed_3857_ = lean_unbox_usize(v_i_3853_);
lean_dec(v_i_3853_);
v_stop_boxed_3858_ = lean_unbox_usize(v_stop_3854_);
lean_dec(v_stop_3854_);
v_res_3859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_5643__boxed_3856_, v_as_3852_, v_i_boxed_3857_, v_stop_boxed_3858_, v_b_3855_);
lean_dec_ref(v_as_3852_);
return v_res_3859_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0));
v___x_3862_ = l_String_toRawSubstring_x27(v___x_3861_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(lean_object* v_as_3879_, size_t v_i_3880_, size_t v_stop_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
uint8_t v___x_3885_; 
v___x_3885_ = lean_usize_dec_eq(v_i_3880_, v_stop_3881_);
if (v___x_3885_ == 0)
{
lean_object* v_quotContext_3886_; lean_object* v_currMacroScope_3887_; lean_object* v_ref_3888_; size_t v___x_3889_; size_t v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_quotContext_3886_ = lean_ctor_get(v___y_3883_, 1);
v_currMacroScope_3887_ = lean_ctor_get(v___y_3883_, 2);
v_ref_3888_ = lean_ctor_get(v___y_3883_, 5);
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_sub(v_i_3880_, v___x_3889_);
v___x_3891_ = lean_array_uget_borrowed(v_as_3879_, v___x_3890_);
v___x_3892_ = l_Lean_SourceInfo_fromRef(v_ref_3888_, v___x_3885_);
v___x_3893_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_3894_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1);
v___x_3895_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4));
lean_inc(v_currMacroScope_3887_);
lean_inc(v_quotContext_3886_);
v___x_3896_ = l_Lean_addMacroScope(v_quotContext_3886_, v___x_3895_, v_currMacroScope_3887_);
v___x_3897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8));
lean_inc_n(v___x_3892_, 2);
v___x_3898_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3892_);
lean_ctor_set(v___x_3898_, 1, v___x_3894_);
lean_ctor_set(v___x_3898_, 2, v___x_3896_);
lean_ctor_set(v___x_3898_, 3, v___x_3897_);
v___x_3899_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3891_);
v___x_3900_ = l_Lean_Syntax_node2(v___x_3892_, v___x_3899_, v___x_3891_, v_b_3882_);
v___x_3901_ = l_Lean_Syntax_node2(v___x_3892_, v___x_3893_, v___x_3898_, v___x_3900_);
v_i_3880_ = v___x_3890_;
v_b_3882_ = v___x_3901_;
goto _start;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v_b_3882_);
lean_ctor_set(v___x_3903_, 1, v___y_3884_);
return v___x_3903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___boxed(lean_object* v_as_3904_, lean_object* v_i_3905_, lean_object* v_stop_3906_, lean_object* v_b_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
size_t v_i_boxed_3910_; size_t v_stop_boxed_3911_; lean_object* v_res_3912_; 
v_i_boxed_3910_ = lean_unbox_usize(v_i_3905_);
lean_dec(v_i_3905_);
v_stop_boxed_3911_ = lean_unbox_usize(v_stop_3906_);
lean_dec(v_stop_3906_);
v_res_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_as_3904_, v_i_boxed_3910_, v_stop_boxed_3911_, v_b_3907_, v___y_3908_, v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec_ref(v_as_3904_);
return v_res_3912_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13(void){
_start:
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
v___x_3947_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12));
v___x_3948_ = l_String_toRawSubstring_x27(v___x_3947_);
return v___x_3948_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3953_ = l_Lean_mkAtom(v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(lean_object* v_x_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3957_; uint8_t v___x_3958_; 
v___x_3957_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1));
lean_inc(v_x_3954_);
v___x_3958_ = l_Lean_Syntax_isOfKind(v_x_3954_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_dec(v_x_3954_);
v___x_3959_ = lean_box(1);
v___x_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
lean_ctor_set(v___x_3960_, 1, v_a_3956_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___y_3964_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_4047_ = l_Lean_Syntax_getArg(v_x_3954_, v___x_3962_);
v___x_4048_ = l_Lean_Syntax_getArgs(v___x_4047_);
lean_dec(v___x_4047_);
v___x_4049_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___x_4050_ = lean_array_get_size(v___x_4048_);
v___x_4051_ = lean_nat_dec_lt(v___x_3961_, v___x_4050_);
if (v___x_4051_ == 0)
{
lean_dec_ref(v___x_4048_);
v___y_3964_ = v___x_4049_;
goto v___jp_3963_;
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; uint8_t v___x_4054_; 
v___x_4052_ = lean_box(v___x_3958_);
v___x_4053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___x_4049_);
v___x_4054_ = lean_nat_dec_le(v___x_4050_, v___x_4050_);
if (v___x_4054_ == 0)
{
if (v___x_4051_ == 0)
{
lean_dec_ref(v___x_4053_);
lean_dec_ref(v___x_4048_);
v___y_3964_ = v___x_4049_;
goto v___jp_3963_;
}
else
{
size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; lean_object* v_snd_4058_; 
v___x_4055_ = ((size_t)0ULL);
v___x_4056_ = lean_usize_of_nat(v___x_4050_);
v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_3958_, v___x_4048_, v___x_4055_, v___x_4056_, v___x_4053_);
lean_dec_ref(v___x_4048_);
v_snd_4058_ = lean_ctor_get(v___x_4057_, 1);
lean_inc(v_snd_4058_);
lean_dec_ref(v___x_4057_);
v___y_3964_ = v_snd_4058_;
goto v___jp_3963_;
}
}
else
{
size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; lean_object* v_snd_4062_; 
v___x_4059_ = ((size_t)0ULL);
v___x_4060_ = lean_usize_of_nat(v___x_4050_);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_3958_, v___x_4048_, v___x_4059_, v___x_4060_, v___x_4053_);
lean_dec_ref(v___x_4048_);
v_snd_4062_ = lean_ctor_get(v___x_4061_, 1);
lean_inc(v_snd_4062_);
lean_dec_ref(v___x_4061_);
v___y_3964_ = v_snd_4062_;
goto v___jp_3963_;
}
}
v___jp_3963_:
{
size_t v_sz_3965_; size_t v___x_3966_; lean_object* v___x_3967_; 
v_sz_3965_ = lean_array_size(v___y_3964_);
v___x_3966_ = ((size_t)0ULL);
v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_3965_, v___x_3966_, v___y_3964_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec(v_x_3954_);
v___x_3968_ = lean_box(1);
v___x_3969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v_a_3956_);
return v___x_3969_;
}
else
{
lean_object* v_val_3970_; lean_object* v___x_3971_; lean_object* v_k_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; uint8_t v___x_3975_; 
v_val_3970_ = lean_ctor_get(v___x_3967_, 0);
lean_inc(v_val_3970_);
lean_dec_ref(v___x_3967_);
v___x_3971_ = lean_unsigned_to_nat(3u);
v_k_3972_ = l_Lean_Syntax_getArg(v_x_3954_, v___x_3971_);
lean_dec(v_x_3954_);
v___x_3973_ = lean_array_get_size(v_val_3970_);
v___x_3974_ = lean_unsigned_to_nat(8u);
v___x_3975_ = lean_nat_dec_lt(v___x_3973_, v___x_3974_);
if (v___x_3975_ == 0)
{
lean_object* v_m_3976_; lean_object* v_quotContext_3977_; lean_object* v_currMacroScope_3978_; lean_object* v_ref_3979_; lean_object* v_y_3980_; lean_object* v_z_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; size_t v_sz_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; size_t v_sz_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_m_3976_ = lean_nat_shiftr(v___x_3973_, v___x_3962_);
v_quotContext_3977_ = lean_ctor_get(v_a_3955_, 1);
v_currMacroScope_3978_ = lean_ctor_get(v_a_3955_, 2);
v_ref_3979_ = lean_ctor_get(v_a_3955_, 5);
lean_inc(v_m_3976_);
v_y_3980_ = l_Array_extract___redArg(v_val_3970_, v_m_3976_, v___x_3973_);
v_z_3981_ = l_Array_extract___redArg(v_val_3970_, v___x_3961_, v_m_3976_);
lean_dec(v_val_3970_);
v___x_3982_ = l_Lean_SourceInfo_fromRef(v_ref_3979_, v___x_3975_);
v___x_3983_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2));
v___x_3984_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3));
lean_inc_n(v___x_3982_, 15);
v___x_3985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3982_);
lean_ctor_set(v___x_3985_, 1, v___x_3983_);
v___x_3986_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5));
v___x_3987_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3988_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3982_);
lean_ctor_set(v___x_3989_, 1, v___x_3987_);
lean_ctor_set(v___x_3989_, 2, v___x_3988_);
lean_inc_ref_n(v___x_3989_, 3);
v___x_3990_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3986_, v___x_3989_);
v___x_3991_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7));
v___x_3992_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9));
v___x_3993_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11));
v___x_3994_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13);
v___x_3995_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14));
lean_inc(v_currMacroScope_3978_);
lean_inc(v_quotContext_3977_);
v___x_3996_ = l_Lean_addMacroScope(v_quotContext_3977_, v___x_3995_, v_currMacroScope_3978_);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3982_);
lean_ctor_set(v___x_3998_, 1, v___x_3994_);
lean_ctor_set(v___x_3998_, 2, v___x_3996_);
lean_ctor_set(v___x_3998_, 3, v___x_3997_);
lean_inc_ref(v___x_3998_);
v___x_3999_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3993_, v___x_3998_);
v___x_4000_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_4001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_3982_);
lean_ctor_set(v___x_4001_, 1, v___x_4000_);
v___x_4002_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15));
v___x_4003_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_3982_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
v_sz_4004_ = lean_array_size(v_y_3980_);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_4004_, v___x_3966_, v_y_3980_);
v___x_4006_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_4007_ = l_Lean_mkSepArray(v___x_4005_, v___x_4006_);
lean_dec_ref(v___x_4005_);
v___x_4008_ = l_Array_append___redArg(v___x_3988_, v___x_4007_);
lean_dec_ref(v___x_4007_);
v___x_4009_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4009_, 0, v___x_3982_);
lean_ctor_set(v___x_4009_, 1, v___x_3987_);
lean_ctor_set(v___x_4009_, 2, v___x_4008_);
v___x_4010_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_3982_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_4013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_3982_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
lean_inc_ref(v___x_4013_);
lean_inc_ref(v___x_4011_);
lean_inc_ref(v___x_4003_);
v___x_4014_ = l_Lean_Syntax_node5(v___x_3982_, v___x_3957_, v___x_4003_, v___x_4009_, v___x_4011_, v_k_3972_, v___x_4013_);
v___x_4015_ = l_Lean_Syntax_node5(v___x_3982_, v___x_3992_, v___x_3999_, v___x_3989_, v___x_3989_, v___x_4001_, v___x_4014_);
v___x_4016_ = l_Lean_Syntax_node1(v___x_3982_, v___x_3991_, v___x_4015_);
v_sz_4017_ = lean_array_size(v_z_3981_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_4017_, v___x_3966_, v_z_3981_);
v___x_4019_ = l_Lean_mkSepArray(v___x_4018_, v___x_4006_);
lean_dec_ref(v___x_4018_);
v___x_4020_ = l_Array_append___redArg(v___x_3988_, v___x_4019_);
lean_dec_ref(v___x_4019_);
v___x_4021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4021_, 0, v___x_3982_);
lean_ctor_set(v___x_4021_, 1, v___x_3987_);
lean_ctor_set(v___x_4021_, 2, v___x_4020_);
v___x_4022_ = l_Lean_Syntax_node5(v___x_3982_, v___x_3957_, v___x_4003_, v___x_4021_, v___x_4011_, v___x_3998_, v___x_4013_);
v___x_4023_ = l_Lean_Syntax_node5(v___x_3982_, v___x_3984_, v___x_3985_, v___x_3990_, v___x_4016_, v___x_3989_, v___x_4022_);
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
lean_ctor_set(v___x_4024_, 1, v_a_3956_);
return v___x_4024_;
}
else
{
uint8_t v___x_4025_; 
v___x_4025_ = lean_nat_dec_lt(v___x_3961_, v___x_3973_);
if (v___x_4025_ == 0)
{
lean_object* v___x_4026_; 
lean_dec(v_val_3970_);
v___x_4026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4026_, 0, v_k_3972_);
lean_ctor_set(v___x_4026_, 1, v_a_3956_);
return v___x_4026_;
}
else
{
size_t v___x_4027_; lean_object* v___x_4028_; 
v___x_4027_ = lean_usize_of_nat(v___x_3973_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_val_3970_, v___x_4027_, v___x_3966_, v_k_3972_, v_a_3955_, v_a_3956_);
lean_dec(v_val_3970_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_a_4030_ = lean_ctor_get(v___x_4028_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4028_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4029_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
v_a_4038_ = lean_ctor_get(v___x_4028_, 0);
v_a_4039_ = lean_ctor_get(v___x_4028_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4028_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_inc(v_a_4038_);
lean_dec(v___x_4028_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4038_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___boxed(lean_object* v_x_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(v_x_4063_, v_a_4064_, v_a_4065_);
lean_dec_ref(v_a_4064_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(lean_object* v_x_4155_){
_start:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1));
v___x_4157_ = l_Lean_Name_append(v_x_4155_, v___x_4156_);
return v___x_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(lean_object* v___x_4164_, size_t v_sz_4165_, size_t v_i_4166_, lean_object* v_bs_4167_){
_start:
{
uint8_t v___x_4168_; 
v___x_4168_ = lean_usize_dec_lt(v_i_4166_, v_sz_4165_);
if (v___x_4168_ == 0)
{
lean_dec(v___x_4164_);
return v_bs_4167_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v_v_4171_; lean_object* v___x_4172_; lean_object* v_bs_x27_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; size_t v___x_4177_; size_t v___x_4178_; lean_object* v___x_4179_; 
v___x_4169_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4170_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_v_4171_ = lean_array_uget(v_bs_4167_, v_i_4166_);
v___x_4172_ = lean_unsigned_to_nat(0u);
v_bs_x27_4173_ = lean_array_uset(v_bs_4167_, v_i_4166_, v___x_4172_);
v___x_4174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1));
lean_inc_n(v___x_4164_, 2);
v___x_4175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4164_);
lean_ctor_set(v___x_4175_, 1, v___x_4169_);
lean_ctor_set(v___x_4175_, 2, v___x_4170_);
v___x_4176_ = l_Lean_Syntax_node2(v___x_4164_, v___x_4174_, v___x_4175_, v_v_4171_);
v___x_4177_ = ((size_t)1ULL);
v___x_4178_ = lean_usize_add(v_i_4166_, v___x_4177_);
v___x_4179_ = lean_array_uset(v_bs_x27_4173_, v_i_4166_, v___x_4176_);
v_i_4166_ = v___x_4178_;
v_bs_4167_ = v___x_4179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___boxed(lean_object* v___x_4181_, lean_object* v_sz_4182_, lean_object* v_i_4183_, lean_object* v_bs_4184_){
_start:
{
size_t v_sz_boxed_4185_; size_t v_i_boxed_4186_; lean_object* v_res_4187_; 
v_sz_boxed_4185_ = lean_unbox_usize(v_sz_4182_);
lean_dec(v_sz_4182_);
v_i_boxed_4186_ = lean_unbox_usize(v_i_4183_);
lean_dec(v_i_4183_);
v_res_4187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___x_4181_, v_sz_boxed_4185_, v_i_boxed_4186_, v_bs_4184_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(size_t v_sz_4188_, size_t v_i_4189_, lean_object* v_bs_4190_){
_start:
{
uint8_t v___x_4191_; 
v___x_4191_ = lean_usize_dec_lt(v_i_4189_, v_sz_4188_);
if (v___x_4191_ == 0)
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_bs_4190_);
return v___x_4192_;
}
else
{
lean_object* v_v_4193_; lean_object* v___x_4194_; uint8_t v___x_4195_; 
v_v_4193_ = lean_array_uget(v_bs_4190_, v_i_4189_);
v___x_4194_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4193_);
v___x_4195_ = l_Lean_Syntax_isOfKind(v_v_4193_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
lean_dec(v_v_4193_);
lean_dec_ref(v_bs_4190_);
v___x_4196_ = lean_box(0);
return v___x_4196_;
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v_bs_x27_4199_; lean_object* v_parents_4200_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4197_ = lean_unsigned_to_nat(0u);
v___x_4198_ = lean_unsigned_to_nat(1u);
v_bs_x27_4199_ = lean_array_uset(v_bs_4190_, v_i_4189_, v___x_4197_);
v_parents_4200_ = l_Lean_Syntax_getArg(v_v_4193_, v___x_4197_);
v___x_4206_ = l_Lean_Syntax_getArg(v_v_4193_, v___x_4198_);
lean_dec(v_v_4193_);
v___x_4207_ = l_Lean_Syntax_isNone(v___x_4206_);
if (v___x_4207_ == 0)
{
uint8_t v___x_4208_; 
v___x_4208_ = l_Lean_Syntax_matchesNull(v___x_4206_, v___x_4198_);
if (v___x_4208_ == 0)
{
lean_object* v___x_4209_; 
lean_dec(v_parents_4200_);
lean_dec_ref(v_bs_x27_4199_);
v___x_4209_ = lean_box(0);
return v___x_4209_;
}
else
{
goto v___jp_4201_;
}
}
else
{
lean_dec(v___x_4206_);
goto v___jp_4201_;
}
v___jp_4201_:
{
size_t v___x_4202_; size_t v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = ((size_t)1ULL);
v___x_4203_ = lean_usize_add(v_i_4189_, v___x_4202_);
v___x_4204_ = lean_array_uset(v_bs_x27_4199_, v_i_4189_, v_parents_4200_);
v_i_4189_ = v___x_4203_;
v_bs_4190_ = v___x_4204_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0___boxed(lean_object* v_sz_4210_, lean_object* v_i_4211_, lean_object* v_bs_4212_){
_start:
{
size_t v_sz_boxed_4213_; size_t v_i_boxed_4214_; lean_object* v_res_4215_; 
v_sz_boxed_4213_ = lean_unbox_usize(v_sz_4210_);
lean_dec(v_sz_4210_);
v_i_boxed_4214_ = lean_unbox_usize(v_i_4211_);
lean_dec(v_i_4211_);
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_boxed_4213_, v_i_boxed_4214_, v_bs_4212_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(lean_object* v_x_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; uint8_t v___x_4274_; 
v___x_4271_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_4272_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_4273_ = ((lean_object*)(l_Lean_Parser_Command_classAbbrev___closed__1));
lean_inc(v_x_4268_);
v___x_4274_ = l_Lean_Syntax_isOfKind(v_x_4268_, v___x_4273_);
if (v___x_4274_ == 0)
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
lean_dec(v_x_4268_);
v___x_4275_ = lean_box(1);
v___x_4276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4275_);
lean_ctor_set(v___x_4276_, 1, v_a_4270_);
return v___x_4276_;
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4277_ = lean_unsigned_to_nat(0u);
v___x_4278_ = l_Lean_Syntax_getArg(v_x_4268_, v___x_4277_);
v___x_4279_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0));
lean_inc(v___x_4278_);
v___x_4280_ = l_Lean_Syntax_isOfKind(v___x_4278_, v___x_4279_);
if (v___x_4280_ == 0)
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
lean_dec(v___x_4278_);
lean_dec(v_x_4268_);
v___x_4281_ = lean_box(1);
v___x_4282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
lean_ctor_set(v___x_4282_, 1, v_a_4270_);
return v___x_4282_;
}
else
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; size_t v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; size_t v___y_4348_; lean_object* v___y_4349_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v_ty_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; 
v___x_4283_ = lean_unsigned_to_nat(3u);
v___x_4284_ = l_Lean_Syntax_getArg(v_x_4268_, v___x_4283_);
v___x_4377_ = lean_unsigned_to_nat(4u);
v___x_4378_ = l_Lean_Syntax_getArg(v_x_4268_, v___x_4377_);
v___x_4412_ = lean_unsigned_to_nat(5u);
v___x_4413_ = l_Lean_Syntax_getArg(v_x_4268_, v___x_4412_);
v___x_4414_ = l_Lean_Syntax_isNone(v___x_4413_);
if (v___x_4414_ == 0)
{
lean_object* v___x_4415_; uint8_t v___x_4416_; 
v___x_4415_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4413_);
v___x_4416_ = l_Lean_Syntax_matchesNull(v___x_4413_, v___x_4415_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_dec(v___x_4413_);
lean_dec(v___x_4378_);
lean_dec(v___x_4284_);
lean_dec(v___x_4278_);
lean_dec(v_x_4268_);
v___x_4417_ = lean_box(1);
v___x_4418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4417_);
lean_ctor_set(v___x_4418_, 1, v_a_4270_);
return v___x_4418_;
}
else
{
lean_object* v___x_4419_; lean_object* v_ty_4420_; lean_object* v___x_4421_; 
v___x_4419_ = lean_unsigned_to_nat(1u);
v_ty_4420_ = l_Lean_Syntax_getArg(v___x_4413_, v___x_4419_);
lean_dec(v___x_4413_);
v___x_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4421_, 0, v_ty_4420_);
v_ty_4380_ = v___x_4421_;
v___y_4381_ = v_a_4269_;
v___y_4382_ = v_a_4270_;
goto v___jp_4379_;
}
}
else
{
lean_object* v___x_4422_; 
lean_dec(v___x_4413_);
v___x_4422_ = lean_box(0);
v_ty_4380_ = v___x_4422_;
v___y_4381_ = v_a_4269_;
v___y_4382_ = v_a_4270_;
goto v___jp_4379_;
}
v___jp_4285_:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; size_t v_sz_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_inc_ref_n(v___y_4293_, 2);
v___x_4300_ = l_Array_append___redArg(v___y_4293_, v___y_4299_);
lean_dec_ref(v___y_4299_);
lean_inc_n(v___y_4287_, 7);
lean_inc_n(v___y_4298_, 21);
v___x_4301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4301_, 0, v___y_4298_);
lean_ctor_set(v___x_4301_, 1, v___y_4287_);
lean_ctor_set(v___x_4301_, 2, v___x_4300_);
lean_inc(v___y_4291_);
v___x_4302_ = l_Lean_Syntax_node2(v___y_4298_, v___y_4291_, v___y_4290_, v___x_4301_);
v___x_4303_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1));
v___x_4304_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2));
v___x_4305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___y_4298_);
lean_ctor_set(v___x_4305_, 1, v___x_4303_);
v_sz_4306_ = lean_array_size(v___y_4288_);
v___x_4307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___y_4298_, v_sz_4306_, v___y_4297_, v___y_4288_);
v___x_4308_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_4309_ = l_Lean_mkSepArray(v___x_4307_, v___x_4308_);
lean_dec_ref(v___x_4307_);
v___x_4310_ = l_Array_append___redArg(v___y_4293_, v___x_4309_);
lean_dec_ref(v___x_4309_);
v___x_4311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4311_, 0, v___y_4298_);
lean_ctor_set(v___x_4311_, 1, v___y_4287_);
lean_ctor_set(v___x_4311_, 2, v___x_4310_);
v___x_4312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4312_, 0, v___y_4298_);
lean_ctor_set(v___x_4312_, 1, v___y_4287_);
lean_ctor_set(v___x_4312_, 2, v___y_4293_);
lean_inc_ref_n(v___x_4312_, 4);
v___x_4313_ = l_Lean_Syntax_node3(v___y_4298_, v___x_4304_, v___x_4305_, v___x_4311_, v___x_4312_);
v___x_4314_ = l_Lean_Syntax_node1(v___y_4298_, v___y_4287_, v___x_4313_);
v___x_4315_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4));
v___x_4316_ = l_Lean_Syntax_node1(v___y_4298_, v___x_4315_, v___x_4312_);
lean_inc(v___y_4292_);
v___x_4317_ = l_Lean_Syntax_node6(v___y_4298_, v___y_4292_, v___y_4295_, v___x_4284_, v___x_4302_, v___x_4314_, v___x_4312_, v___x_4316_);
lean_inc(v___y_4296_);
v___x_4318_ = l_Lean_Syntax_node2(v___y_4298_, v___y_4296_, v___x_4278_, v___x_4317_);
v___x_4319_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5));
v___x_4320_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6));
v___x_4321_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4321_, 0, v___y_4298_);
lean_ctor_set(v___x_4321_, 1, v___x_4319_);
v___x_4322_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_4323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___y_4298_);
lean_ctor_set(v___x_4323_, 1, v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
lean_inc_ref_n(v___y_4294_, 2);
v___x_4325_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___y_4294_, v___x_4324_);
v___x_4326_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6));
v___x_4327_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___y_4294_, v___x_4326_);
v___x_4328_ = l_Lean_Syntax_node1(v___y_4298_, v___x_4327_, v___x_4312_);
v___x_4329_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7));
v___x_4330_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8));
v___x_4331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___y_4298_);
lean_ctor_set(v___x_4331_, 1, v___x_4329_);
v___x_4332_ = l_Lean_Syntax_node2(v___y_4298_, v___x_4330_, v___x_4331_, v___x_4312_);
v___x_4333_ = l_Lean_Syntax_node2(v___y_4298_, v___x_4325_, v___x_4328_, v___x_4332_);
v___x_4334_ = l_Lean_Syntax_node1(v___y_4298_, v___y_4287_, v___x_4333_);
v___x_4335_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_4336_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___y_4298_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_Syntax_node1(v___y_4298_, v___y_4287_, v___y_4289_);
v___x_4338_ = l_Lean_Syntax_node5(v___y_4298_, v___x_4320_, v___x_4321_, v___x_4323_, v___x_4334_, v___x_4336_, v___x_4337_);
v___x_4339_ = l_Lean_Syntax_node2(v___y_4298_, v___y_4287_, v___x_4318_, v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4339_);
lean_ctor_set(v___x_4340_, 1, v___y_4286_);
return v___x_4340_;
}
v___jp_4341_:
{
lean_object* v_ref_4350_; uint8_t v___x_4351_; lean_object* v_ctor_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; size_t v_sz_4363_; lean_object* v___x_4364_; size_t v_sz_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v_ref_4350_ = lean_ctor_get(v___y_4346_, 5);
v___x_4351_ = 0;
v_ctor_4352_ = l_Lean_mkIdentFrom(v___x_4284_, v___y_4349_, v___x_4351_);
v___x_4353_ = l_Lean_SourceInfo_fromRef(v_ref_4350_, v___x_4351_);
v___x_4354_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4355_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9));
v___x_4356_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11));
v___x_4357_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13));
v___x_4358_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14));
lean_inc_n(v___x_4353_, 3);
v___x_4359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4353_);
lean_ctor_set(v___x_4359_, 1, v___x_4358_);
v___x_4360_ = l_Lean_Syntax_node1(v___x_4353_, v___x_4357_, v___x_4359_);
v___x_4361_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15));
v___x_4362_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4363_ = lean_array_size(v___y_4342_);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_4363_, v___y_4348_, v___y_4342_);
v_sz_4365_ = lean_array_size(v___x_4364_);
v___x_4366_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_4365_, v___y_4348_, v___x_4364_);
v___x_4367_ = l_Array_append___redArg(v___x_4362_, v___x_4366_);
lean_dec_ref(v___x_4366_);
v___x_4368_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4353_);
lean_ctor_set(v___x_4368_, 1, v___x_4354_);
lean_ctor_set(v___x_4368_, 2, v___x_4367_);
if (lean_obj_tag(v___y_4345_) == 1)
{
lean_object* v_val_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_val_4369_ = lean_ctor_get(v___y_4345_, 0);
lean_inc(v_val_4369_);
lean_dec_ref(v___y_4345_);
v___x_4370_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref(v___y_4347_);
v___x_4371_ = l_Lean_Name_mkStr4(v___x_4271_, v___x_4272_, v___y_4347_, v___x_4370_);
v___x_4372_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
lean_inc_n(v___x_4353_, 2);
v___x_4373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4353_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l_Lean_Syntax_node2(v___x_4353_, v___x_4371_, v___x_4373_, v_val_4369_);
v___x_4375_ = l_Array_mkArray1___redArg(v___x_4374_);
v___y_4286_ = v___y_4343_;
v___y_4287_ = v___x_4354_;
v___y_4288_ = v___y_4344_;
v___y_4289_ = v_ctor_4352_;
v___y_4290_ = v___x_4368_;
v___y_4291_ = v___x_4361_;
v___y_4292_ = v___x_4356_;
v___y_4293_ = v___x_4362_;
v___y_4294_ = v___y_4347_;
v___y_4295_ = v___x_4360_;
v___y_4296_ = v___x_4355_;
v___y_4297_ = v___y_4348_;
v___y_4298_ = v___x_4353_;
v___y_4299_ = v___x_4375_;
goto v___jp_4285_;
}
else
{
lean_object* v___x_4376_; 
lean_dec(v___y_4345_);
v___x_4376_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___y_4286_ = v___y_4343_;
v___y_4287_ = v___x_4354_;
v___y_4288_ = v___y_4344_;
v___y_4289_ = v_ctor_4352_;
v___y_4290_ = v___x_4368_;
v___y_4291_ = v___x_4361_;
v___y_4292_ = v___x_4356_;
v___y_4293_ = v___x_4362_;
v___y_4294_ = v___y_4347_;
v___y_4295_ = v___x_4360_;
v___y_4296_ = v___x_4355_;
v___y_4297_ = v___y_4348_;
v___y_4298_ = v___x_4353_;
v___y_4299_ = v___x_4376_;
goto v___jp_4285_;
}
}
v___jp_4379_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; size_t v_sz_4386_; size_t v___x_4387_; lean_object* v___x_4388_; 
v___x_4383_ = lean_unsigned_to_nat(7u);
v___x_4384_ = l_Lean_Syntax_getArg(v_x_4268_, v___x_4383_);
lean_dec(v_x_4268_);
v___x_4385_ = l_Lean_Syntax_getArgs(v___x_4384_);
lean_dec(v___x_4384_);
v_sz_4386_ = lean_array_size(v___x_4385_);
v___x_4387_ = ((size_t)0ULL);
v___x_4388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_4386_, v___x_4387_, v___x_4385_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
lean_dec(v_ty_4380_);
lean_dec(v___x_4378_);
lean_dec(v___x_4284_);
lean_dec(v___x_4278_);
v___x_4389_ = lean_box(1);
v___x_4390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
lean_ctor_set(v___x_4390_, 1, v___y_4382_);
return v___x_4390_;
}
else
{
lean_object* v_val_4391_; lean_object* v___x_4392_; lean_object* v_params_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; uint8_t v___x_4396_; 
v_val_4391_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_val_4391_);
lean_dec_ref(v___x_4388_);
v___x_4392_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v_params_4393_ = l_Lean_Syntax_getArgs(v___x_4378_);
lean_dec(v___x_4378_);
v___x_4394_ = l_Lean_Syntax_getArg(v___x_4284_, v___x_4277_);
v___x_4395_ = l_Lean_Syntax_getId(v___x_4394_);
lean_dec(v___x_4394_);
v___x_4396_ = l_Lean_Name_hasMacroScopes(v___x_4395_);
if (v___x_4396_ == 0)
{
lean_object* v___x_4397_; 
v___x_4397_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v___x_4395_);
v___y_4342_ = v_params_4393_;
v___y_4343_ = v___y_4382_;
v___y_4344_ = v_val_4391_;
v___y_4345_ = v_ty_4380_;
v___y_4346_ = v___y_4381_;
v___y_4347_ = v___x_4392_;
v___y_4348_ = v___x_4387_;
v___y_4349_ = v___x_4397_;
goto v___jp_4341_;
}
else
{
lean_object* v_view_4398_; lean_object* v_name_4399_; lean_object* v_imported_4400_; lean_object* v_ctx_4401_; lean_object* v_scopes_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4411_; 
v_view_4398_ = l_Lean_extractMacroScopes(v___x_4395_);
v_name_4399_ = lean_ctor_get(v_view_4398_, 0);
v_imported_4400_ = lean_ctor_get(v_view_4398_, 1);
v_ctx_4401_ = lean_ctor_get(v_view_4398_, 2);
v_scopes_4402_ = lean_ctor_get(v_view_4398_, 3);
v_isSharedCheck_4411_ = !lean_is_exclusive(v_view_4398_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4404_ = v_view_4398_;
v_isShared_4405_ = v_isSharedCheck_4411_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_scopes_4402_);
lean_inc(v_ctx_4401_);
lean_inc(v_imported_4400_);
lean_inc(v_name_4399_);
lean_dec(v_view_4398_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4411_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4408_; 
v___x_4406_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v_name_4399_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 0, v___x_4406_);
v___x_4408_ = v___x_4404_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4406_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_imported_4400_);
lean_ctor_set(v_reuseFailAlloc_4410_, 2, v_ctx_4401_);
lean_ctor_set(v_reuseFailAlloc_4410_, 3, v_scopes_4402_);
v___x_4408_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_MacroScopesView_review(v___x_4408_);
v___y_4342_ = v_params_4393_;
v___y_4343_ = v___y_4382_;
v___y_4344_ = v_val_4391_;
v___y_4345_ = v_ty_4380_;
v___y_4346_ = v___y_4381_;
v___y_4347_ = v___x_4392_;
v___y_4348_ = v___x_4387_;
v___y_4349_ = v___x_4409_;
goto v___jp_4341_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___boxed(lean_object* v_x_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(v_x_4423_, v_a_4424_, v_a_4425_);
lean_dec_ref(v_a_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(size_t v_sz_4511_, size_t v_i_4512_, lean_object* v_bs_4513_){
_start:
{
uint8_t v___x_4514_; 
v___x_4514_ = lean_usize_dec_lt(v_i_4512_, v_sz_4511_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; 
v___x_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4515_, 0, v_bs_4513_);
return v___x_4515_;
}
else
{
lean_object* v_v_4516_; lean_object* v___x_4517_; uint8_t v___x_4518_; 
v_v_4516_ = lean_array_uget(v_bs_4513_, v_i_4512_);
v___x_4517_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4516_);
v___x_4518_ = l_Lean_Syntax_isOfKind(v_v_4516_, v___x_4517_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; 
lean_dec(v_v_4516_);
lean_dec_ref(v_bs_4513_);
v___x_4519_ = lean_box(0);
return v___x_4519_;
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v_bs_x27_4522_; lean_object* v_ts_4523_; size_t v___x_4524_; size_t v___x_4525_; lean_object* v___x_4526_; 
v___x_4520_ = lean_unsigned_to_nat(1u);
v___x_4521_ = lean_unsigned_to_nat(0u);
v_bs_x27_4522_ = lean_array_uset(v_bs_4513_, v_i_4512_, v___x_4521_);
v_ts_4523_ = l_Lean_Syntax_getArg(v_v_4516_, v___x_4520_);
lean_dec(v_v_4516_);
v___x_4524_ = ((size_t)1ULL);
v___x_4525_ = lean_usize_add(v_i_4512_, v___x_4524_);
v___x_4526_ = lean_array_uset(v_bs_x27_4522_, v_i_4512_, v_ts_4523_);
v_i_4512_ = v___x_4525_;
v_bs_4513_ = v___x_4526_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0___boxed(lean_object* v_sz_4528_, lean_object* v_i_4529_, lean_object* v_bs_4530_){
_start:
{
size_t v_sz_boxed_4531_; size_t v_i_boxed_4532_; lean_object* v_res_4533_; 
v_sz_boxed_4531_ = lean_unbox_usize(v_sz_4528_);
lean_dec(v_sz_4528_);
v_i_boxed_4532_ = lean_unbox_usize(v_i_4529_);
lean_dec(v_i_4529_);
v_res_4533_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_boxed_4531_, v_i_boxed_4532_, v_bs_4530_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(lean_object* v___x_4540_, size_t v_sz_4541_, size_t v_i_4542_, lean_object* v_bs_4543_){
_start:
{
uint8_t v___x_4544_; 
v___x_4544_ = lean_usize_dec_lt(v_i_4542_, v_sz_4541_);
if (v___x_4544_ == 0)
{
lean_dec(v___x_4540_);
return v_bs_4543_;
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v_v_4548_; lean_object* v___x_4549_; lean_object* v_bs_x27_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; size_t v___x_4570_; size_t v___x_4571_; lean_object* v___x_4572_; 
v___x_4545_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4546_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4547_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v_v_4548_ = lean_array_uget(v_bs_4543_, v_i_4542_);
v___x_4549_ = lean_unsigned_to_nat(0u);
v_bs_x27_4550_ = lean_array_uset(v_bs_4543_, v_i_4542_, v___x_4549_);
v___x_4551_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_4552_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
lean_inc_n(v___x_4540_, 11);
v___x_4553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4540_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_4555_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_4556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4540_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
v___x_4557_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4540_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = l_Lean_Syntax_node3(v___x_4540_, v___x_4554_, v___x_4556_, v_v_4548_, v___x_4558_);
v___x_4560_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_4561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4540_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
v___x_4562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0));
v___x_4563_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1));
v___x_4564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4540_);
lean_ctor_set(v___x_4564_, 1, v___x_4562_);
v___x_4565_ = l_Lean_Syntax_node1(v___x_4540_, v___x_4563_, v___x_4564_);
v___x_4566_ = l_Lean_Syntax_node3(v___x_4540_, v___x_4546_, v___x_4559_, v___x_4561_, v___x_4565_);
v___x_4567_ = l_Lean_Syntax_node1(v___x_4540_, v___x_4545_, v___x_4566_);
v___x_4568_ = l_Lean_Syntax_node1(v___x_4540_, v___x_4547_, v___x_4567_);
v___x_4569_ = l_Lean_Syntax_node2(v___x_4540_, v___x_4551_, v___x_4553_, v___x_4568_);
v___x_4570_ = ((size_t)1ULL);
v___x_4571_ = lean_usize_add(v_i_4542_, v___x_4570_);
v___x_4572_ = lean_array_uset(v_bs_x27_4550_, v_i_4542_, v___x_4569_);
v_i_4542_ = v___x_4571_;
v_bs_4543_ = v___x_4572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___boxed(lean_object* v___x_4574_, lean_object* v_sz_4575_, lean_object* v_i_4576_, lean_object* v_bs_4577_){
_start:
{
size_t v_sz_boxed_4578_; size_t v_i_boxed_4579_; lean_object* v_res_4580_; 
v_sz_boxed_4578_ = lean_unbox_usize(v_sz_4575_);
lean_dec(v_sz_4575_);
v_i_boxed_4579_ = lean_unbox_usize(v_i_4576_);
lean_dec(v_i_4576_);
v_res_4580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4574_, v_sz_boxed_4578_, v_i_boxed_4579_, v_bs_4577_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(lean_object* v_x_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_){
_start:
{
lean_object* v___x_4596_; uint8_t v___x_4597_; 
v___x_4596_ = ((lean_object*)(l_Lean_solveTactic___closed__1));
lean_inc(v_x_4593_);
v___x_4597_ = l_Lean_Syntax_isOfKind(v_x_4593_, v___x_4596_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; lean_object* v___x_4599_; 
lean_dec(v_x_4593_);
v___x_4598_ = lean_box(1);
v___x_4599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4599_, 0, v___x_4598_);
lean_ctor_set(v___x_4599_, 1, v_a_4595_);
return v___x_4599_;
}
else
{
lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; size_t v_sz_4603_; size_t v___x_4604_; lean_object* v___x_4605_; 
v___x_4600_ = lean_unsigned_to_nat(1u);
v___x_4601_ = l_Lean_Syntax_getArg(v_x_4593_, v___x_4600_);
lean_dec(v_x_4593_);
v___x_4602_ = l_Lean_Syntax_getArgs(v___x_4601_);
lean_dec(v___x_4601_);
v_sz_4603_ = lean_array_size(v___x_4602_);
v___x_4604_ = ((size_t)0ULL);
v___x_4605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_4603_, v___x_4604_, v___x_4602_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v___x_4606_; lean_object* v___x_4607_; 
v___x_4606_ = lean_box(1);
v___x_4607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4607_, 0, v___x_4606_);
lean_ctor_set(v___x_4607_, 1, v_a_4595_);
return v___x_4607_;
}
else
{
lean_object* v_val_4608_; lean_object* v_ref_4609_; uint8_t v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; size_t v_sz_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v_val_4608_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_val_4608_);
lean_dec_ref(v___x_4605_);
v_ref_4609_ = lean_ctor_get(v_a_4594_, 5);
v___x_4610_ = 0;
v___x_4611_ = l_Lean_SourceInfo_fromRef(v_ref_4609_, v___x_4610_);
v___x_4612_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0));
v___x_4613_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1));
lean_inc_n(v___x_4611_, 8);
v___x_4614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4614_, 0, v___x_4611_);
lean_ctor_set(v___x_4614_, 1, v___x_4612_);
v___x_4615_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_4616_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4617_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4618_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2));
v___x_4619_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3));
v___x_4620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4620_, 0, v___x_4611_);
lean_ctor_set(v___x_4620_, 1, v___x_4618_);
v___x_4621_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4622_ = lean_array_size(v_val_4608_);
v___x_4623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4611_, v_sz_4622_, v___x_4604_, v_val_4608_);
v___x_4624_ = l_Array_append___redArg(v___x_4621_, v___x_4623_);
lean_dec_ref(v___x_4623_);
v___x_4625_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4625_, 0, v___x_4611_);
lean_ctor_set(v___x_4625_, 1, v___x_4617_);
lean_ctor_set(v___x_4625_, 2, v___x_4624_);
v___x_4626_ = l_Lean_Syntax_node2(v___x_4611_, v___x_4619_, v___x_4620_, v___x_4625_);
v___x_4627_ = l_Lean_Syntax_node1(v___x_4611_, v___x_4617_, v___x_4626_);
v___x_4628_ = l_Lean_Syntax_node1(v___x_4611_, v___x_4616_, v___x_4627_);
v___x_4629_ = l_Lean_Syntax_node1(v___x_4611_, v___x_4615_, v___x_4628_);
v___x_4630_ = l_Lean_Syntax_node2(v___x_4611_, v___x_4613_, v___x_4614_, v___x_4629_);
v___x_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4630_);
lean_ctor_set(v___x_4631_, 1, v_a_4595_);
return v___x_4631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___boxed(lean_object* v_x_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(v_x_4632_, v_a_4633_, v_a_4634_);
lean_dec_ref(v_a_4633_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(lean_object* v___x_4664_, size_t v_sz_4665_, size_t v_i_4666_, lean_object* v_bs_4667_){
_start:
{
uint8_t v___x_4668_; 
v___x_4668_ = lean_usize_dec_lt(v_i_4666_, v_sz_4665_);
if (v___x_4668_ == 0)
{
lean_dec(v___x_4664_);
return v_bs_4667_;
}
else
{
lean_object* v___x_4669_; lean_object* v_v_4670_; lean_object* v___x_4671_; lean_object* v_bs_x27_4672_; lean_object* v___x_4673_; size_t v___x_4674_; size_t v___x_4675_; lean_object* v___x_4676_; 
v___x_4669_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v_v_4670_ = lean_array_uget(v_bs_4667_, v_i_4666_);
v___x_4671_ = lean_unsigned_to_nat(0u);
v_bs_x27_4672_ = lean_array_uset(v_bs_4667_, v_i_4666_, v___x_4671_);
lean_inc(v___x_4664_);
v___x_4673_ = l_Lean_Syntax_node1(v___x_4664_, v___x_4669_, v_v_4670_);
v___x_4674_ = ((size_t)1ULL);
v___x_4675_ = lean_usize_add(v_i_4666_, v___x_4674_);
v___x_4676_ = lean_array_uset(v_bs_x27_4672_, v_i_4666_, v___x_4673_);
v_i_4666_ = v___x_4675_;
v_bs_4667_ = v___x_4676_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0___boxed(lean_object* v___x_4678_, lean_object* v_sz_4679_, lean_object* v_i_4680_, lean_object* v_bs_4681_){
_start:
{
size_t v_sz_boxed_4682_; size_t v_i_boxed_4683_; lean_object* v_res_4684_; 
v_sz_boxed_4682_ = lean_unbox_usize(v_sz_4679_);
lean_dec(v_sz_4679_);
v_i_boxed_4683_ = lean_unbox_usize(v_i_4680_);
lean_dec(v_i_4680_);
v_res_4684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4678_, v_sz_boxed_4682_, v_i_boxed_4683_, v_bs_4681_);
return v_res_4684_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11(void){
_start:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4719_ = l_Lean_mkAtom(v___x_4718_);
return v___x_4719_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13(void){
_start:
{
lean_object* v___x_4721_; lean_object* v___x_4722_; 
v___x_4721_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12));
v___x_4722_ = l_String_toRawSubstring_x27(v___x_4721_);
return v___x_4722_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20(void){
_start:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19));
v___x_4737_ = l_String_toRawSubstring_x27(v___x_4736_);
return v___x_4737_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25(void){
_start:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15));
v___x_4750_ = l_String_toRawSubstring_x27(v___x_4749_);
return v___x_4750_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(lean_object* v_x_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v___x_4767_; uint8_t v___x_4768_; 
v___x_4767_ = ((lean_object*)(l_Lean_term__Matches___x7c___closed__1));
lean_inc(v_x_4764_);
v___x_4768_ = l_Lean_Syntax_isOfKind(v_x_4764_, v___x_4767_);
if (v___x_4768_ == 0)
{
lean_object* v___x_4769_; lean_object* v___x_4770_; 
lean_dec(v_x_4764_);
v___x_4769_ = lean_box(1);
v___x_4770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4769_);
lean_ctor_set(v___x_4770_, 1, v_a_4766_);
return v___x_4770_;
}
else
{
lean_object* v_quotContext_4771_; lean_object* v_currMacroScope_4772_; lean_object* v_ref_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v_p_4778_; uint8_t v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; size_t v_sz_4810_; size_t v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v_quotContext_4771_ = lean_ctor_get(v_a_4765_, 1);
v_currMacroScope_4772_ = lean_ctor_get(v_a_4765_, 2);
v_ref_4773_ = lean_ctor_get(v_a_4765_, 5);
v___x_4774_ = lean_unsigned_to_nat(0u);
v___x_4775_ = l_Lean_Syntax_getArg(v_x_4764_, v___x_4774_);
v___x_4776_ = lean_unsigned_to_nat(2u);
v___x_4777_ = l_Lean_Syntax_getArg(v_x_4764_, v___x_4776_);
lean_dec(v_x_4764_);
v_p_4778_ = l_Lean_Syntax_getArgs(v___x_4777_);
lean_dec(v___x_4777_);
v___x_4779_ = 0;
v___x_4780_ = l_Lean_SourceInfo_fromRef(v_ref_4773_, v___x_4779_);
v___x_4781_ = ((lean_object*)(l_unexpandExists___closed__1));
v___x_4782_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_4783_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_4780_, 29);
v___x_4784_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4780_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_4786_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_4787_ = lean_box(0);
lean_inc_n(v_currMacroScope_4772_, 4);
lean_inc_n(v_quotContext_4771_, 4);
v___x_4788_ = l_Lean_addMacroScope(v_quotContext_4771_, v___x_4787_, v_currMacroScope_4772_);
v___x_4789_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0));
v___x_4790_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4780_);
lean_ctor_set(v___x_4790_, 1, v___x_4786_);
lean_ctor_set(v___x_4790_, 2, v___x_4788_);
lean_ctor_set(v___x_4790_, 3, v___x_4789_);
v___x_4791_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4785_, v___x_4790_);
v___x_4792_ = l_Lean_Syntax_node2(v___x_4780_, v___x_4782_, v___x_4784_, v___x_4791_);
v___x_4793_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1));
v___x_4794_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2));
v___x_4795_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3));
v___x_4796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4780_);
lean_ctor_set(v___x_4796_, 1, v___x_4794_);
v___x_4797_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4798_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4780_);
lean_ctor_set(v___x_4799_, 1, v___x_4797_);
lean_ctor_set(v___x_4799_, 2, v___x_4798_);
v___x_4800_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5));
lean_inc_ref_n(v___x_4799_, 2);
v___x_4801_ = l_Lean_Syntax_node2(v___x_4780_, v___x_4800_, v___x_4799_, v___x_4775_);
v___x_4802_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4797_, v___x_4801_);
v___x_4803_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6));
v___x_4804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4780_);
lean_ctor_set(v___x_4804_, 1, v___x_4803_);
v___x_4805_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8));
v___x_4806_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10));
v___x_4807_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4808_, 0, v___x_4780_);
lean_ctor_set(v___x_4808_, 1, v___x_4807_);
v___x_4809_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_p_4778_);
lean_dec_ref(v_p_4778_);
v_sz_4810_ = lean_array_size(v___x_4809_);
v___x_4811_ = ((size_t)0ULL);
v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4780_, v_sz_4810_, v___x_4811_, v___x_4809_);
v___x_4813_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11);
v___x_4814_ = l_Lean_mkSepArray(v___x_4812_, v___x_4813_);
lean_dec_ref(v___x_4812_);
v___x_4815_ = l_Array_append___redArg(v___x_4798_, v___x_4814_);
lean_dec_ref(v___x_4814_);
v___x_4816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4780_);
lean_ctor_set(v___x_4816_, 1, v___x_4797_);
lean_ctor_set(v___x_4816_, 2, v___x_4815_);
v___x_4817_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_4818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4780_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13);
v___x_4820_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14));
v___x_4821_ = l_Lean_addMacroScope(v_quotContext_4771_, v___x_4820_, v_currMacroScope_4772_);
v___x_4822_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18));
v___x_4823_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4780_);
lean_ctor_set(v___x_4823_, 1, v___x_4819_);
lean_ctor_set(v___x_4823_, 2, v___x_4821_);
lean_ctor_set(v___x_4823_, 3, v___x_4822_);
lean_inc_ref(v___x_4818_);
lean_inc_ref(v___x_4808_);
v___x_4824_ = l_Lean_Syntax_node4(v___x_4780_, v___x_4806_, v___x_4808_, v___x_4816_, v___x_4818_, v___x_4823_);
v___x_4825_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11));
v___x_4826_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_4827_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4827_, 0, v___x_4780_);
lean_ctor_set(v___x_4827_, 1, v___x_4826_);
v___x_4828_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4825_, v___x_4827_);
v___x_4829_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4797_, v___x_4828_);
v___x_4830_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4797_, v___x_4829_);
v___x_4831_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20);
v___x_4832_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21));
v___x_4833_ = l_Lean_addMacroScope(v_quotContext_4771_, v___x_4832_, v_currMacroScope_4772_);
v___x_4834_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24));
v___x_4835_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4780_);
lean_ctor_set(v___x_4835_, 1, v___x_4831_);
lean_ctor_set(v___x_4835_, 2, v___x_4833_);
lean_ctor_set(v___x_4835_, 3, v___x_4834_);
v___x_4836_ = l_Lean_Syntax_node4(v___x_4780_, v___x_4806_, v___x_4808_, v___x_4830_, v___x_4818_, v___x_4835_);
v___x_4837_ = l_Lean_Syntax_node2(v___x_4780_, v___x_4797_, v___x_4824_, v___x_4836_);
v___x_4838_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4805_, v___x_4837_);
v___x_4839_ = l_Lean_Syntax_node6(v___x_4780_, v___x_4795_, v___x_4796_, v___x_4799_, v___x_4799_, v___x_4802_, v___x_4804_, v___x_4838_);
v___x_4840_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4841_, 0, v___x_4780_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
lean_inc_ref(v___x_4841_);
lean_inc(v___x_4792_);
v___x_4842_ = l_Lean_Syntax_node3(v___x_4780_, v___x_4793_, v___x_4792_, v___x_4839_, v___x_4841_);
v___x_4843_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_4844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4780_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
v___x_4845_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25);
v___x_4846_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26));
v___x_4847_ = l_Lean_addMacroScope(v_quotContext_4771_, v___x_4846_, v_currMacroScope_4772_);
v___x_4848_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30));
v___x_4849_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4780_);
lean_ctor_set(v___x_4849_, 1, v___x_4845_);
lean_ctor_set(v___x_4849_, 2, v___x_4847_);
lean_ctor_set(v___x_4849_, 3, v___x_4848_);
v___x_4850_ = l_Lean_Syntax_node1(v___x_4780_, v___x_4797_, v___x_4849_);
v___x_4851_ = l_Lean_Syntax_node5(v___x_4780_, v___x_4781_, v___x_4792_, v___x_4842_, v___x_4844_, v___x_4850_, v___x_4841_);
v___x_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
lean_ctor_set(v___x_4852_, 1, v_a_4766_);
return v___x_4852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___boxed(lean_object* v_x_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v_res_4856_; 
v_res_4856_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(v_x_4853_, v_a_4854_, v_a_4855_);
lean_dec_ref(v_a_4854_);
return v_res_4856_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1(void){
_start:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0));
v___x_4884_ = l_String_toRawSubstring_x27(v___x_4883_);
return v___x_4884_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8(void){
_start:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7));
v___x_4899_ = l_String_toRawSubstring_x27(v___x_4898_);
return v___x_4899_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(lean_object* v_x_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v___x_4915_; uint8_t v___x_4916_; 
v___x_4915_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v_x_4912_);
v___x_4916_ = l_Lean_Syntax_isOfKind(v_x_4912_, v___x_4915_);
if (v___x_4916_ == 0)
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
lean_dec(v_x_4912_);
v___x_4917_ = lean_box(1);
v___x_4918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4917_);
lean_ctor_set(v___x_4918_, 1, v_a_4914_);
return v___x_4918_;
}
else
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; uint8_t v___x_4922_; 
v___x_4919_ = lean_unsigned_to_nat(0u);
v___x_4920_ = lean_unsigned_to_nat(1u);
v___x_4921_ = l_Lean_Syntax_getArg(v_x_4912_, v___x_4920_);
lean_dec(v_x_4912_);
lean_inc(v___x_4921_);
v___x_4922_ = l_Lean_Syntax_matchesNull(v___x_4921_, v___x_4920_);
if (v___x_4922_ == 0)
{
lean_object* v___x_4923_; lean_object* v___x_4924_; uint8_t v___x_4925_; 
v___x_4923_ = lean_unsigned_to_nat(2u);
v___x_4924_ = l_Lean_Syntax_getNumArgs(v___x_4921_);
v___x_4925_ = lean_nat_dec_le(v___x_4923_, v___x_4924_);
if (v___x_4925_ == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_dec(v___x_4924_);
lean_dec(v___x_4921_);
v___x_4926_ = lean_box(1);
v___x_4927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
lean_ctor_set(v___x_4927_, 1, v_a_4914_);
return v___x_4927_;
}
else
{
lean_object* v_quotContext_4928_; lean_object* v_currMacroScope_4929_; lean_object* v_ref_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
v_quotContext_4928_ = lean_ctor_get(v_a_4913_, 1);
v_currMacroScope_4929_ = lean_ctor_get(v_a_4913_, 2);
v_ref_4930_ = lean_ctor_get(v_a_4913_, 5);
v___x_4931_ = l_Lean_Syntax_getArg(v___x_4921_, v___x_4919_);
v___x_4932_ = l_Lean_Syntax_getArgs(v___x_4921_);
lean_dec(v___x_4921_);
v___x_4933_ = l_Array_extract___redArg(v___x_4932_, v___x_4923_, v___x_4924_);
lean_dec_ref(v___x_4932_);
v___x_4934_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4935_ = lean_box(2);
v___x_4936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4935_);
lean_ctor_set(v___x_4936_, 1, v___x_4934_);
lean_ctor_set(v___x_4936_, 2, v___x_4933_);
v___x_4937_ = l_Lean_Syntax_getArgs(v___x_4936_);
lean_dec_ref(v___x_4936_);
v___x_4938_ = l_Lean_SourceInfo_fromRef(v_ref_4930_, v___x_4922_);
v___x_4939_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4940_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1);
v___x_4941_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2));
lean_inc(v_currMacroScope_4929_);
lean_inc(v_quotContext_4928_);
v___x_4942_ = l_Lean_addMacroScope(v_quotContext_4928_, v___x_4941_, v_currMacroScope_4929_);
v___x_4943_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6));
lean_inc_n(v___x_4938_, 6);
v___x_4944_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4938_);
lean_ctor_set(v___x_4944_, 1, v___x_4940_);
lean_ctor_set(v___x_4944_, 2, v___x_4942_);
lean_ctor_set(v___x_4944_, 3, v___x_4943_);
v___x_4945_ = ((lean_object*)(l_unexpandSubtype___closed__2));
v___x_4946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4938_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
v___x_4947_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4948_ = l_Array_append___redArg(v___x_4947_, v___x_4937_);
lean_dec_ref(v___x_4937_);
v___x_4949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4938_);
lean_ctor_set(v___x_4949_, 1, v___x_4934_);
lean_ctor_set(v___x_4949_, 2, v___x_4948_);
v___x_4950_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4938_);
lean_ctor_set(v___x_4951_, 1, v___x_4950_);
v___x_4952_ = l_Lean_Syntax_node3(v___x_4938_, v___x_4915_, v___x_4946_, v___x_4949_, v___x_4951_);
v___x_4953_ = l_Lean_Syntax_node2(v___x_4938_, v___x_4934_, v___x_4931_, v___x_4952_);
v___x_4954_ = l_Lean_Syntax_node2(v___x_4938_, v___x_4939_, v___x_4944_, v___x_4953_);
v___x_4955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v_a_4914_);
return v___x_4955_;
}
}
else
{
lean_object* v_quotContext_4956_; lean_object* v_currMacroScope_4957_; lean_object* v_ref_4958_; lean_object* v___x_4959_; uint8_t v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v_quotContext_4956_ = lean_ctor_get(v_a_4913_, 1);
v_currMacroScope_4957_ = lean_ctor_get(v_a_4913_, 2);
v_ref_4958_ = lean_ctor_get(v_a_4913_, 5);
v___x_4959_ = l_Lean_Syntax_getArg(v___x_4921_, v___x_4919_);
lean_dec(v___x_4921_);
v___x_4960_ = 0;
v___x_4961_ = l_Lean_SourceInfo_fromRef(v_ref_4958_, v___x_4960_);
v___x_4962_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4963_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8);
v___x_4964_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9));
lean_inc(v_currMacroScope_4957_);
lean_inc(v_quotContext_4956_);
v___x_4965_ = l_Lean_addMacroScope(v_quotContext_4956_, v___x_4964_, v_currMacroScope_4957_);
v___x_4966_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13));
lean_inc_n(v___x_4961_, 2);
v___x_4967_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4967_, 0, v___x_4961_);
lean_ctor_set(v___x_4967_, 1, v___x_4963_);
lean_ctor_set(v___x_4967_, 2, v___x_4965_);
lean_ctor_set(v___x_4967_, 3, v___x_4966_);
v___x_4968_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4969_ = l_Lean_Syntax_node1(v___x_4961_, v___x_4968_, v___x_4959_);
v___x_4970_ = l_Lean_Syntax_node2(v___x_4961_, v___x_4962_, v___x_4967_, v___x_4969_);
v___x_4971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4971_, 0, v___x_4970_);
lean_ctor_set(v___x_4971_, 1, v_a_4914_);
return v___x_4971_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___boxed(lean_object* v_x_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(v_x_4972_, v_a_4973_, v_a_4974_);
lean_dec_ref(v_a_4973_);
return v_res_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander(lean_object* v_x_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_){
_start:
{
lean_object* v___x_4979_; uint8_t v___x_4980_; 
v___x_4979_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_4976_);
v___x_4980_ = l_Lean_Syntax_isOfKind(v_x_4976_, v___x_4979_);
if (v___x_4980_ == 0)
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
lean_dec(v_x_4976_);
v___x_4981_ = lean_box(0);
v___x_4982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
lean_ctor_set(v___x_4982_, 1, v_a_4978_);
return v___x_4982_;
}
else
{
lean_object* v___x_4983_; lean_object* v___x_4984_; uint8_t v___x_4985_; 
v___x_4983_ = lean_unsigned_to_nat(1u);
v___x_4984_ = l_Lean_Syntax_getArg(v_x_4976_, v___x_4983_);
lean_dec(v_x_4976_);
lean_inc(v___x_4984_);
v___x_4985_ = l_Lean_Syntax_matchesNull(v___x_4984_, v___x_4983_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; lean_object* v___x_4987_; 
lean_dec(v___x_4984_);
v___x_4986_ = lean_box(0);
v___x_4987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v_a_4978_);
return v___x_4987_;
}
else
{
lean_object* v___x_4988_; lean_object* v___x_4989_; uint8_t v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4988_ = lean_unsigned_to_nat(0u);
v___x_4989_ = l_Lean_Syntax_getArg(v___x_4984_, v___x_4988_);
lean_dec(v___x_4984_);
v___x_4990_ = 0;
v___x_4991_ = l_Lean_SourceInfo_fromRef(v_a_4977_, v___x_4990_);
v___x_4992_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
v___x_4993_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_4991_, 3);
v___x_4994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4991_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4996_ = l_Lean_Syntax_node1(v___x_4991_, v___x_4995_, v___x_4989_);
v___x_4997_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4998_, 0, v___x_4991_);
lean_ctor_set(v___x_4998_, 1, v___x_4997_);
v___x_4999_ = l_Lean_Syntax_node3(v___x_4991_, v___x_4992_, v___x_4994_, v___x_4996_, v___x_4998_);
v___x_5000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v_a_4978_);
return v___x_5000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander___boxed(lean_object* v_x_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_){
_start:
{
lean_object* v_res_5004_; 
v_res_5004_ = l_Lean_singletonUnexpander(v_x_5001_, v_a_5002_, v_a_5003_);
lean_dec(v_a_5002_);
return v_res_5004_;
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander(lean_object* v_x_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_){
_start:
{
lean_object* v___x_5008_; uint8_t v___x_5009_; 
v___x_5008_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_5005_);
v___x_5009_ = l_Lean_Syntax_isOfKind(v_x_5005_, v___x_5008_);
if (v___x_5009_ == 0)
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
lean_dec(v_x_5005_);
v___x_5010_ = lean_box(0);
v___x_5011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5010_);
lean_ctor_set(v___x_5011_, 1, v_a_5007_);
return v___x_5011_;
}
else
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; uint8_t v___x_5015_; 
v___x_5012_ = lean_unsigned_to_nat(1u);
v___x_5013_ = l_Lean_Syntax_getArg(v_x_5005_, v___x_5012_);
lean_dec(v_x_5005_);
v___x_5014_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5013_);
v___x_5015_ = l_Lean_Syntax_matchesNull(v___x_5013_, v___x_5014_);
if (v___x_5015_ == 0)
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
lean_dec(v___x_5013_);
v___x_5016_ = lean_box(0);
v___x_5017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5016_);
lean_ctor_set(v___x_5017_, 1, v_a_5007_);
return v___x_5017_;
}
else
{
lean_object* v___x_5018_; lean_object* v___x_5019_; uint8_t v___x_5020_; 
v___x_5018_ = l_Lean_Syntax_getArg(v___x_5013_, v___x_5012_);
v___x_5019_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v___x_5018_);
v___x_5020_ = l_Lean_Syntax_isOfKind(v___x_5018_, v___x_5019_);
if (v___x_5020_ == 0)
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
lean_dec(v___x_5018_);
lean_dec(v___x_5013_);
v___x_5021_ = lean_box(0);
v___x_5022_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
lean_ctor_set(v___x_5022_, 1, v_a_5007_);
return v___x_5022_;
}
else
{
lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5023_ = lean_unsigned_to_nat(0u);
v___x_5024_ = l_Lean_Syntax_getArg(v___x_5013_, v___x_5023_);
lean_dec(v___x_5013_);
v___x_5025_ = l_Lean_Syntax_getArg(v___x_5018_, v___x_5012_);
lean_dec(v___x_5018_);
v___x_5026_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_5027_ = l_Lean_Syntax_getArgs(v___x_5025_);
lean_dec(v___x_5025_);
v___x_5028_ = 0;
v___x_5029_ = l_Lean_SourceInfo_fromRef(v_a_5006_, v___x_5028_);
v___x_5030_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_5029_, 4);
v___x_5031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5031_, 0, v___x_5029_);
lean_ctor_set(v___x_5031_, 1, v___x_5030_);
v___x_5032_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_5033_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5029_);
lean_ctor_set(v___x_5033_, 1, v___x_5026_);
v___x_5034_ = l_Array_mkArray2___redArg(v___x_5024_, v___x_5033_);
v___x_5035_ = l_Array_append___redArg(v___x_5034_, v___x_5027_);
lean_dec_ref(v___x_5027_);
v___x_5036_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5036_, 0, v___x_5029_);
lean_ctor_set(v___x_5036_, 1, v___x_5032_);
lean_ctor_set(v___x_5036_, 2, v___x_5035_);
v___x_5037_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_5038_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5029_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = l_Lean_Syntax_node3(v___x_5029_, v___x_5019_, v___x_5031_, v___x_5036_, v___x_5038_);
v___x_5040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5039_);
lean_ctor_set(v___x_5040_, 1, v_a_5007_);
return v___x_5040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander___boxed(lean_object* v_x_5041_, lean_object* v_a_5042_, lean_object* v_a_5043_){
_start:
{
lean_object* v_res_5044_; 
v_res_5044_ = l_Lean_insertUnexpander(v_x_5041_, v_a_5042_, v_a_5043_);
lean_dec(v_a_5042_);
return v_res_5044_;
}
}
lean_object* runtime_initialize_Init_Conv(uint8_t builtin);
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_unbracketedExplicitBinders = _init_l_Lean_unbracketedExplicitBinders();
lean_mark_persistent(l_Lean_unbracketedExplicitBinders);
l_Lean_bracketedExplicitBinders = _init_l_Lean_bracketedExplicitBinders();
lean_mark_persistent(l_Lean_bracketedExplicitBinders);
l_Lean_explicitBinders = _init_l_Lean_explicitBinders();
lean_mark_persistent(l_Lean_explicitBinders);
l_term_u2203___x2c__ = _init_l_term_u2203___x2c__();
lean_mark_persistent(l_term_u2203___x2c__);
l_termExists___x2c__ = _init_l_termExists___x2c__();
lean_mark_persistent(l_termExists___x2c__);
l_term_u03a3___x2c__ = _init_l_term_u03a3___x2c__();
lean_mark_persistent(l_term_u03a3___x2c__);
l_term_u03a3_x27___x2c__ = _init_l_term_u03a3_x27___x2c__();
lean_mark_persistent(l_term_u03a3_x27___x2c__);
l_term___xd7____1 = _init_l_term___xd7____1();
lean_mark_persistent(l_term___xd7____1);
l_term___xd7_x27____1 = _init_l_term___xd7_x27____1();
lean_mark_persistent(l_term___xd7_x27____1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Conv(uint8_t builtin);
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_Meta_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Conv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_NotationExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_NotationExtra(builtin);
}
#ifdef __cplusplus
}
#endif
