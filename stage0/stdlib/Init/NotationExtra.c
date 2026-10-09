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
lean_object* l_Array_mkArray0___redArg();
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
static const lean_ctor_object l_term_x7b___x7d___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__31_value),((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__18_value)}};
static const lean_object* l_term_x7b___x7d___closed__3 = (const lean_object*)&l_term_x7b___x7d___closed__3_value;
static const lean_ctor_object l_term_x7b___x7d___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_term_x7b___x7d___closed__3_value),((lean_object*)&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17_value),((lean_object*)&l_Lean_unifConstraintElem___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_term_x7b___x7d___closed__4 = (const lean_object*)&l_term_x7b___x7d___closed__4_value;
static const lean_ctor_object l_term_x7b___x7d___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_term_x7b___x7d___closed__2_value),((lean_object*)&l_term_x7b___x7d___closed__4_value)}};
static const lean_object* l_term_x7b___x7d___closed__5 = (const lean_object*)&l_term_x7b___x7d___closed__5_value;
static const lean_ctor_object l_term_x7b___x7d___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_unexpandSubtype___closed__4_value)}};
static const lean_object* l_term_x7b___x7d___closed__6 = (const lean_object*)&l_term_x7b___x7d___closed__6_value;
static const lean_ctor_object l_term_x7b___x7d___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_unbracketedExplicitBinders___closed__4_value),((lean_object*)&l_term_x7b___x7d___closed__5_value),((lean_object*)&l_term_x7b___x7d___closed__6_value)}};
static const lean_object* l_term_x7b___x7d___closed__7 = (const lean_object*)&l_term_x7b___x7d___closed__7_value;
static const lean_ctor_object l_term_x7b___x7d___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_term_x7b___x7d___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_term_x7b___x7d___closed__7_value)}};
static const lean_object* l_term_x7b___x7d___closed__8 = (const lean_object*)&l_term_x7b___x7d___closed__8_value;
LEAN_EXPORT const lean_object* l_term_x7b___x7d = (const lean_object*)&l_term_x7b___x7d___closed__8_value;
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
v___x_152_ = l_Array_mkArray0___redArg();
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
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(uint8_t v___x_362_, lean_object* v_as_363_, size_t v_i_364_, size_t v_stop_365_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_362_ = stack[0].m_num;
lean_object* v_as_363_ = stack[1].m_obj;
size_t v_i_364_ = stack[2].m_num;
size_t v_stop_365_ = stack[3].m_num;
uint8_t v_res_376_;
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_362_, v_as_363_, v_i_364_, v_stop_365_);
stack->m_num = v_res_376_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0___boxed(lean_object* v___x_377_, lean_object* v_as_378_, lean_object* v_i_379_, lean_object* v_stop_380_){
_start:
{
uint8_t v___x_803__boxed_381_; size_t v_i_boxed_382_; size_t v_stop_boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v___x_803__boxed_381_ = lean_unbox(v___x_377_);
v_i_boxed_382_ = lean_unbox_usize(v_i_379_);
lean_dec(v_i_379_);
v_stop_boxed_383_ = lean_unbox_usize(v_stop_380_);
lean_dec(v_stop_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_803__boxed_381_, v_as_378_, v_i_boxed_382_, v_stop_boxed_383_);
lean_dec_ref(v_as_378_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders(lean_object* v_combinatorDeclName_387_, lean_object* v_explicitBinders_388_, lean_object* v_body_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_ref_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_ref_392_ = lean_ctor_get(v_a_390_, 5);
v___x_393_ = 0;
v___x_394_ = l_Lean_mkCIdentFrom(v_ref_392_, v_combinatorDeclName_387_, v___x_393_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_Lean_Syntax_getArg(v_explicitBinders_388_, v___x_395_);
lean_inc(v___x_396_);
v___x_397_ = l_Lean_Syntax_getKind(v___x_396_);
v___x_398_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_399_ = lean_name_eq(v___x_397_, v___x_398_);
lean_dec(v___x_397_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_Syntax_getArgs(v___x_396_);
lean_dec(v___x_396_);
v___x_401_ = lean_array_get_size(v___x_400_);
v___x_402_ = lean_nat_dec_lt(v___x_395_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_expandBracketedBindersAux(v___x_394_, v___x_400_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_400_);
return v___x_403_;
}
else
{
if (v___x_402_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = l_Lean_expandBracketedBindersAux(v___x_394_, v___x_400_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_400_);
return v___x_404_;
}
else
{
size_t v___x_405_; size_t v___x_406_; uint8_t v___x_407_; 
v___x_405_ = ((size_t)0ULL);
v___x_406_ = lean_usize_of_nat(v___x_401_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_399_, v___x_400_, v___x_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_expandBracketedBindersAux(v___x_394_, v___x_400_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_400_);
return v___x_408_;
}
else
{
if (v___x_399_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec_ref(v___x_400_);
lean_dec(v___x_394_);
lean_dec(v_body_389_);
v___x_409_ = ((lean_object*)(l_Lean_expandExplicitBinders___closed__0));
v___x_410_ = l_Lean_Macro_throwError___redArg(v___x_409_, v_a_390_, v_a_391_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_expandBracketedBindersAux(v___x_394_, v___x_400_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_400_);
return v___x_411_;
}
}
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_412_ = l_Lean_Syntax_getArg(v___x_396_, v___x_395_);
v___x_413_ = l_Lean_Syntax_getArgs(v___x_412_);
lean_dec(v___x_412_);
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = l_Lean_Syntax_getArg(v___x_396_, v___x_414_);
lean_dec(v___x_396_);
v___x_416_ = l_Lean_Syntax_isNone(v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = l_Lean_Syntax_getArg(v___x_415_, v___x_414_);
lean_dec(v___x_415_);
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = l_Lean_expandExplicitBindersAux(v___x_394_, v___x_413_, v___x_418_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_413_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v___x_415_);
v___x_420_ = lean_box(0);
v___x_421_ = l_Lean_expandExplicitBindersAux(v___x_394_, v___x_413_, v___x_420_, v_body_389_, v_a_390_, v_a_391_);
lean_dec_ref(v___x_413_);
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders___boxed(lean_object* v_combinatorDeclName_422_, lean_object* v_explicitBinders_423_, lean_object* v_body_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_expandExplicitBinders(v_combinatorDeclName_422_, v_explicitBinders_423_, v_body_424_, v_a_425_, v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_explicitBinders_423_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders(lean_object* v_combinatorDeclName_428_, lean_object* v_bracketedExplicitBinders_429_, lean_object* v_body_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_ref_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_ref_433_ = lean_ctor_get(v_a_431_, 5);
v___x_434_ = 0;
v___x_435_ = l_Lean_mkCIdentFrom(v_ref_433_, v_combinatorDeclName_428_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(1u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_array_push(v___x_437_, v_bracketedExplicitBinders_429_);
v___x_439_ = l_Lean_expandBracketedBindersAux(v___x_435_, v___x_438_, v_body_430_, v_a_431_, v_a_432_);
lean_dec_ref(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders___boxed(lean_object* v_combinatorDeclName_440_, lean_object* v_bracketedExplicitBinders_441_, lean_object* v_body_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_expandBracketedBinders(v_combinatorDeclName_440_, v_bracketedExplicitBinders_441_, v_body_442_, v_a_443_, v_a_444_);
lean_dec_ref(v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(lean_object* v_____do__lift_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_652_ = 0;
v___x_653_ = l_Lean_SourceInfo_fromRef(v_____do__lift_649_, v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v___y_651_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0___boxed(lean_object* v_____do__lift_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_____do__lift_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v_____do__lift_655_);
return v_res_658_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(size_t v_sz_659_, size_t v_i_660_, lean_object* v_bs_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = lean_usize_dec_lt(v_i_660_, v_sz_659_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; 
v___x_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_663_, 0, v_bs_661_);
return v___x_663_;
}
else
{
lean_object* v_v_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_v_664_ = lean_array_uget_borrowed(v_bs_661_, v_i_660_);
v___x_665_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__1));
lean_inc(v_v_664_);
v___x_666_ = l_Lean_Syntax_isOfKind(v_v_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_bs_661_);
v___x_667_ = lean_box(0);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = l_Lean_Syntax_getArg(v_v_664_, v___x_668_);
v___x_670_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_669_);
v___x_671_ = l_Lean_Syntax_isOfKind(v___x_669_, v___x_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_dec(v___x_669_);
lean_dec_ref(v_bs_661_);
v___x_672_ = lean_box(0);
return v___x_672_;
}
else
{
lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_673_ = lean_unsigned_to_nat(1u);
v___x_674_ = l_Lean_Syntax_getArg(v_v_664_, v___x_673_);
v___x_675_ = l_Lean_Syntax_matchesNull(v___x_674_, v___x_668_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_dec(v___x_669_);
lean_dec_ref(v_bs_661_);
v___x_676_ = lean_box(0);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v_bs_x27_678_; lean_object* v_cs_u2081_679_; lean_object* v_cs_u2082_680_; lean_object* v___x_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___x_677_ = lean_unsigned_to_nat(2u);
v_bs_x27_678_ = lean_array_uset(v_bs_661_, v_i_660_, v___x_668_);
v_cs_u2081_679_ = l_Lean_Syntax_getArg(v___x_669_, v___x_668_);
v_cs_u2082_680_ = l_Lean_Syntax_getArg(v___x_669_, v___x_677_);
lean_dec(v___x_669_);
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v_cs_u2081_679_);
lean_ctor_set(v___x_681_, 1, v_cs_u2082_680_);
v___x_682_ = ((size_t)1ULL);
v___x_683_ = lean_usize_add(v_i_660_, v___x_682_);
v___x_684_ = lean_array_uset(v_bs_x27_678_, v_i_660_, v___x_681_);
v_i_660_ = v___x_683_;
v_bs_661_ = v___x_684_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_659_ = stack[0].m_num;
size_t v_i_660_ = stack[1].m_num;
lean_object* v_bs_661_ = stack[2].m_obj;
lean_object* v_res_686_;
v_res_686_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_659_, v_i_660_, v_bs_661_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0___boxed(lean_object* v_sz_687_, lean_object* v_i_688_, lean_object* v_bs_689_){
_start:
{
size_t v_sz_boxed_690_; size_t v_i_boxed_691_; lean_object* v_res_692_; 
v_sz_boxed_690_ = lean_unbox_usize(v_sz_687_);
lean_dec(v_sz_687_);
v_i_boxed_691_ = lean_unbox_usize(v_i_688_);
lean_dec(v_i_688_);
v_res_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_boxed_690_, v_i_boxed_691_, v_bs_689_);
return v_res_692_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(lean_object* v_as_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
uint8_t v___x_710_; 
v___x_710_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v_b_707_);
lean_ctor_set(v___x_711_, 1, v___y_709_);
return v___x_711_;
}
else
{
lean_object* v_a_712_; lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_734_; 
v_a_712_ = lean_array_uget(v_as_704_, v_i_706_);
v_fst_713_ = lean_ctor_get(v_a_712_, 0);
v_snd_714_ = lean_ctor_get(v_a_712_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_734_ == 0)
{
v___x_716_ = v_a_712_;
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_a_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_734_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_ref_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v_ref_718_ = lean_ctor_get(v___y_708_, 5);
v___x_719_ = 0;
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_718_, v___x_719_);
v___x_721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1));
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_723_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v___x_720_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 2);
lean_ctor_set(v___x_716_, 1, v___x_723_);
lean_ctor_set(v___x_716_, 0, v___x_720_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_733_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; size_t v___x_730_; size_t v___x_731_; 
lean_inc_n(v___x_720_, 2);
v___x_726_ = l_Lean_Syntax_node3(v___x_720_, v___x_722_, v_fst_713_, v___x_725_, v_snd_714_);
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_720_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_Syntax_node3(v___x_720_, v___x_721_, v___x_726_, v___x_728_, v_b_707_);
v___x_730_ = ((size_t)1ULL);
v___x_731_ = lean_usize_add(v_i_706_, v___x_730_);
v_i_706_ = v___x_731_;
v_b_707_ = v___x_729_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_704_ = stack[0].m_obj;
size_t v_sz_705_ = stack[1].m_num;
size_t v_i_706_ = stack[2].m_num;
lean_object* v_b_707_ = stack[3].m_obj;
lean_object* v___y_708_ = stack[4].m_obj;
lean_object* v___y_709_ = stack[5].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v_as_704_, v_sz_705_, v_i_706_, v_b_707_, v___y_708_, v___y_709_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___boxed(lean_object* v_as_736_, lean_object* v_sz_737_, lean_object* v_i_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
size_t v_sz_boxed_742_; size_t v_i_boxed_743_; lean_object* v_res_744_; 
v_sz_boxed_742_ = lean_unbox_usize(v_sz_737_);
lean_dec(v_sz_737_);
v_i_boxed_743_ = lean_unbox_usize(v_i_738_);
lean_dec(v_i_738_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v_as_736_, v_sz_boxed_742_, v_i_boxed_743_, v_b_739_, v___y_740_, v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec_ref(v_as_736_);
return v_res_744_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(size_t v_sz_745_, size_t v_i_746_, lean_object* v_bs_747_){
_start:
{
uint8_t v___x_748_; 
v___x_748_ = lean_usize_dec_lt(v_i_746_, v_sz_745_);
if (v___x_748_ == 0)
{
return v_bs_747_;
}
else
{
lean_object* v_v_749_; lean_object* v___x_750_; lean_object* v_bs_x27_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v_v_749_ = lean_array_uget(v_bs_747_, v_i_746_);
v___x_750_ = lean_unsigned_to_nat(0u);
v_bs_x27_751_ = lean_array_uset(v_bs_747_, v_i_746_, v___x_750_);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_746_, v___x_752_);
v___x_754_ = lean_array_uset(v_bs_x27_751_, v_i_746_, v_v_749_);
v_i_746_ = v___x_753_;
v_bs_747_ = v___x_754_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_745_ = stack[0].m_num;
size_t v_i_746_ = stack[1].m_num;
lean_object* v_bs_747_ = stack[2].m_obj;
lean_object* v_res_756_;
v_res_756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_745_, v_i_746_, v_bs_747_);
stack->m_obj
 = v_res_756_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5___boxed(lean_object* v_sz_757_, lean_object* v_i_758_, lean_object* v_bs_759_){
_start:
{
size_t v_sz_boxed_760_; size_t v_i_boxed_761_; lean_object* v_res_762_; 
v_sz_boxed_760_ = lean_unbox_usize(v_sz_757_);
lean_dec(v_sz_757_);
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_res_762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_boxed_760_, v_i_boxed_761_, v_bs_759_);
return v_res_762_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(size_t v_sz_763_, size_t v_i_764_, lean_object* v_bs_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_764_, v_sz_763_);
if (v___x_766_ == 0)
{
return v_bs_765_;
}
else
{
lean_object* v_v_767_; lean_object* v___x_768_; lean_object* v_bs_x27_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v_v_767_ = lean_array_uget(v_bs_765_, v_i_764_);
v___x_768_ = lean_unsigned_to_nat(0u);
v_bs_x27_769_ = lean_array_uset(v_bs_765_, v_i_764_, v___x_768_);
v___x_770_ = ((size_t)1ULL);
v___x_771_ = lean_usize_add(v_i_764_, v___x_770_);
v___x_772_ = lean_array_uset(v_bs_x27_769_, v_i_764_, v_v_767_);
v_i_764_ = v___x_771_;
v_bs_765_ = v___x_772_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_763_ = stack[0].m_num;
size_t v_i_764_ = stack[1].m_num;
lean_object* v_bs_765_ = stack[2].m_obj;
lean_object* v_res_774_;
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_763_, v_i_764_, v_bs_765_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4___boxed(lean_object* v_sz_775_, lean_object* v_i_776_, lean_object* v_bs_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_775_);
lean_dec(v_sz_775_);
v_i_boxed_779_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_boxed_778_, v_i_boxed_779_, v_bs_777_);
return v_res_780_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(size_t v_sz_781_, size_t v_i_782_, lean_object* v_bs_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_lt(v_i_782_, v_sz_781_);
if (v___x_784_ == 0)
{
return v_bs_783_;
}
else
{
lean_object* v_v_785_; lean_object* v_fst_786_; lean_object* v___x_787_; lean_object* v_bs_x27_788_; size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v_v_785_ = lean_array_uget_borrowed(v_bs_783_, v_i_782_);
v_fst_786_ = lean_ctor_get(v_v_785_, 0);
lean_inc(v_fst_786_);
v___x_787_ = lean_unsigned_to_nat(0u);
v_bs_x27_788_ = lean_array_uset(v_bs_783_, v_i_782_, v___x_787_);
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_add(v_i_782_, v___x_789_);
v___x_791_ = lean_array_uset(v_bs_x27_788_, v_i_782_, v_fst_786_);
v_i_782_ = v___x_790_;
v_bs_783_ = v___x_791_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_781_ = stack[0].m_num;
size_t v_i_782_ = stack[1].m_num;
lean_object* v_bs_783_ = stack[2].m_obj;
lean_object* v_res_793_;
v_res_793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_781_, v_i_782_, v_bs_783_);
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2___boxed(lean_object* v_sz_794_, lean_object* v_i_795_, lean_object* v_bs_796_){
_start:
{
size_t v_sz_boxed_797_; size_t v_i_boxed_798_; lean_object* v_res_799_; 
v_sz_boxed_797_ = lean_unbox_usize(v_sz_794_);
lean_dec(v_sz_794_);
v_i_boxed_798_ = lean_unbox_usize(v_i_795_);
lean_dec(v_i_795_);
v_res_799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_boxed_797_, v_i_boxed_798_, v_bs_796_);
return v_res_799_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(size_t v_sz_800_, size_t v_i_801_, lean_object* v_bs_802_){
_start:
{
uint8_t v___x_803_; 
v___x_803_ = lean_usize_dec_lt(v_i_801_, v_sz_800_);
if (v___x_803_ == 0)
{
return v_bs_802_;
}
else
{
lean_object* v_v_804_; lean_object* v_snd_805_; lean_object* v___x_806_; lean_object* v_bs_x27_807_; size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
v_v_804_ = lean_array_uget_borrowed(v_bs_802_, v_i_801_);
v_snd_805_ = lean_ctor_get(v_v_804_, 1);
lean_inc(v_snd_805_);
v___x_806_ = lean_unsigned_to_nat(0u);
v_bs_x27_807_ = lean_array_uset(v_bs_802_, v_i_801_, v___x_806_);
v___x_808_ = ((size_t)1ULL);
v___x_809_ = lean_usize_add(v_i_801_, v___x_808_);
v___x_810_ = lean_array_uset(v_bs_x27_807_, v_i_801_, v_snd_805_);
v_i_801_ = v___x_809_;
v_bs_802_ = v___x_810_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_800_ = stack[0].m_num;
size_t v_i_801_ = stack[1].m_num;
lean_object* v_bs_802_ = stack[2].m_obj;
lean_object* v_res_812_;
v_res_812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_800_, v_i_801_, v_bs_802_);
stack->m_obj
 = v_res_812_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1___boxed(lean_object* v_sz_813_, lean_object* v_i_814_, lean_object* v_bs_815_){
_start:
{
size_t v_sz_boxed_816_; size_t v_i_boxed_817_; lean_object* v_res_818_; 
v_sz_boxed_816_ = lean_unbox_usize(v_sz_813_);
lean_dec(v_sz_813_);
v_i_boxed_817_ = lean_unbox_usize(v_i_814_);
lean_dec(v_i_814_);
v_res_818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_boxed_816_, v_i_boxed_817_, v_bs_815_);
return v_res_818_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14));
v___x_836_ = l_String_toRawSubstring_x27(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18));
v___x_842_ = l_String_toRawSubstring_x27(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27));
v___x_853_ = l_String_toRawSubstring_x27(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(lean_object* v_x_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_875_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_876_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1));
lean_inc(v_x_872_);
v___x_877_ = l_Lean_Syntax_isOfKind(v_x_872_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_dec(v_x_872_);
v___x_878_ = lean_box(1);
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_a_874_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; lean_object* v___y_882_; size_t v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___y_896_; lean_object* v___y_897_; lean_object* v___y_898_; lean_object* v___y_899_; lean_object* v___y_947_; lean_object* v___y_948_; size_t v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_1014_; lean_object* v___y_1015_; size_t v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1024_; lean_object* v___y_1025_; lean_object* v___y_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; lean_object* v___y_1029_; lean_object* v___y_1030_; lean_object* v___y_1031_; lean_object* v___y_1079_; lean_object* v___y_1080_; size_t v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1146_; lean_object* v___y_1147_; size_t v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; size_t v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1278_; lean_object* v___y_1279_; size_t v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; size_t v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; size_t v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v_doc_x3f_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_1562_ = l_Lean_Syntax_getArg(v_x_872_, v___x_880_);
v___x_1563_ = l_Lean_Syntax_isNone(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1562_);
v___x_1565_ = l_Lean_Syntax_matchesNull(v___x_1562_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec(v___x_1562_);
lean_dec(v_x_872_);
v___x_1566_ = lean_box(1);
v___x_1567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
lean_ctor_set(v___x_1567_, 1, v_a_874_);
return v___x_1567_;
}
else
{
lean_object* v_doc_x3f_1568_; 
v_doc_x3f_1568_ = l_Lean_Syntax_getArg(v___x_1562_, v___x_880_);
lean_dec(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1571_; uint8_t v___x_1572_; 
v___x_1571_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36));
lean_inc(v_doc_x3f_1568_);
v___x_1572_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1568_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
lean_dec(v_doc_x3f_1568_);
lean_dec(v_x_872_);
v___x_1573_ = lean_box(1);
v___x_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v_a_874_);
return v___x_1574_;
}
else
{
goto v___jp_1569_;
}
}
else
{
goto v___jp_1569_;
}
v___jp_1569_:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v_doc_x3f_1568_);
v_doc_x3f_1515_ = v___x_1570_;
v___y_1516_ = v_a_873_;
v___y_1517_ = v_a_874_;
goto v___jp_1514_;
}
}
}
else
{
lean_object* v___x_1575_; 
lean_dec(v___x_1562_);
v___x_1575_ = lean_box(0);
v_doc_x3f_1515_ = v___x_1575_;
v___y_1516_ = v_a_873_;
v___y_1517_ = v_a_874_;
goto v___jp_1514_;
}
v___jp_881_:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; size_t v_sz_910_; lean_object* v___x_911_; size_t v_sz_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_900_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_901_ = lean_box(2);
lean_inc_n(v___y_886_, 4);
v___x_902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v___y_886_);
lean_ctor_set(v___x_902_, 2, v___x_900_);
v___x_903_ = lean_mk_empty_array_with_capacity(v___y_889_);
v___x_904_ = lean_array_push(v___x_903_, v___y_899_);
v___x_905_ = lean_array_push(v___x_904_, v___x_902_);
v___x_906_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_906_, 0, v___x_901_);
lean_ctor_set(v___x_906_, 1, v___y_888_);
lean_ctor_set(v___x_906_, 2, v___x_905_);
v___x_907_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_898_);
lean_inc_ref_n(v___y_892_, 6);
v___x_908_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___y_898_, v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_910_ = lean_array_size(v___y_887_);
v___x_911_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_910_, v___y_883_, v___y_887_);
v_sz_912_ = lean_array_size(v___x_911_);
v___x_913_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_912_, v___y_883_, v___x_911_);
lean_inc_ref(v___y_895_);
v___x_914_ = l_Array_append___redArg(v___y_895_, v___x_913_);
lean_dec_ref(v___x_913_);
lean_inc_n(v___y_890_, 14);
v___x_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_915_, 0, v___y_890_);
lean_ctor_set(v___x_915_, 1, v___y_886_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
v___x_916_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_882_, 2);
v___x_917_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___y_882_, v___x_916_);
v___x_918_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___y_890_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_921_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___y_882_, v___x_920_);
v___x_922_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___y_890_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_925_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___x_924_, v___x_909_);
v___x_926_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_927_, 0, v___y_890_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_Syntax_node1(v___y_890_, v___x_925_, v___x_927_);
v___x_929_ = l_Lean_Syntax_node1(v___y_890_, v___y_886_, v___x_928_);
v___x_930_ = l_Lean_Syntax_node2(v___y_890_, v___x_921_, v___x_923_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node2(v___y_890_, v___x_917_, v___x_919_, v___x_930_);
v___x_932_ = l_Lean_Syntax_node1(v___y_890_, v___y_886_, v___x_931_);
v___x_933_ = l_Lean_Syntax_node2(v___y_890_, v___x_908_, v___x_915_, v___x_932_);
v___x_934_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_935_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___y_898_, v___x_934_);
v___x_936_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_937_, 0, v___y_890_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_939_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_940_ = l_Lean_Name_mkStr4(v___x_875_, v___y_892_, v___x_938_, v___x_939_);
lean_inc_n(v___y_891_, 3);
v___x_941_ = l_Lean_Syntax_node2(v___y_890_, v___x_940_, v___y_891_, v___y_891_);
v___x_942_ = l_Lean_Syntax_node4(v___y_890_, v___x_935_, v___x_937_, v___y_894_, v___x_941_, v___y_891_);
v___x_943_ = l_Lean_Syntax_node5(v___y_890_, v___y_897_, v___y_885_, v___x_906_, v___x_933_, v___x_942_, v___y_891_);
v___x_944_ = l_Lean_Syntax_node2(v___y_890_, v___y_893_, v___y_884_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___y_896_);
return v___x_945_;
}
v___jp_946_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_inc_ref_n(v___y_962_, 2);
v___x_968_ = l_Array_append___redArg(v___y_962_, v___y_967_);
lean_dec_ref(v___y_967_);
lean_inc_n(v___y_951_, 5);
lean_inc_n(v___y_955_, 20);
v___x_969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_969_, 0, v___y_955_);
lean_ctor_set(v___x_969_, 1, v___y_951_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_948_, 2);
lean_inc_ref_n(v___y_957_, 6);
v___x_971_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___y_948_, v___x_970_);
v___x_972_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___y_955_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_975_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___y_948_, v___x_974_);
v___x_976_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_977_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_978_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___x_976_, v___x_977_);
v___x_979_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_980_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_947_);
lean_inc(v___y_956_);
v___x_981_ = l_Lean_addMacroScope(v___y_956_, v___x_980_, v___y_947_);
lean_inc_n(v___y_953_, 2);
v___x_982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_982_, 0, v___y_955_);
lean_ctor_set(v___x_982_, 1, v___x_979_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_ctor_set(v___x_982_, 3, v___y_953_);
v___x_983_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_983_, 0, v___y_955_);
lean_ctor_set(v___x_983_, 1, v___y_951_);
lean_ctor_set(v___x_983_, 2, v___y_962_);
lean_inc_ref_n(v___x_983_, 7);
lean_inc(v___x_978_);
v___x_984_ = l_Lean_Syntax_node2(v___y_955_, v___x_978_, v___x_982_, v___x_983_);
lean_inc(v___x_975_);
v___x_985_ = l_Lean_Syntax_node2(v___y_955_, v___x_975_, v___y_950_, v___x_984_);
v___x_986_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_987_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_987_, 0, v___y_955_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
lean_inc(v___y_964_);
v___x_988_ = l_Lean_Syntax_node1(v___y_955_, v___y_964_, v___x_983_);
v___x_989_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_990_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_991_ = l_Lean_addMacroScope(v___y_956_, v___x_990_, v___y_947_);
v___x_992_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_992_, 0, v___y_955_);
lean_ctor_set(v___x_992_, 1, v___x_989_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
lean_ctor_set(v___x_992_, 3, v___y_953_);
v___x_993_ = l_Lean_Syntax_node2(v___y_955_, v___x_978_, v___x_992_, v___x_983_);
v___x_994_ = l_Lean_Syntax_node2(v___y_955_, v___x_975_, v___x_988_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node3(v___y_955_, v___y_951_, v___x_985_, v___x_987_, v___x_994_);
v___x_996_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_997_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_997_, 0, v___y_955_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_Syntax_node3(v___y_955_, v___x_971_, v___x_973_, v___x_995_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node1(v___y_955_, v___y_951_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_966_, 3);
v___x_1001_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___y_966_, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___y_955_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
v___x_1003_ = l_Lean_Syntax_node1(v___y_955_, v___x_1001_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node1(v___y_955_, v___y_951_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node7(v___y_955_, v___y_965_, v___x_969_, v___x_999_, v___x_1004_, v___x_983_, v___x_983_, v___x_983_, v___x_983_);
v___x_1006_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1007_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___y_966_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___y_955_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1011_ = l_Lean_Name_mkStr4(v___x_875_, v___y_957_, v___y_966_, v___x_1010_);
if (lean_obj_tag(v___y_960_) == 0)
{
v___y_882_ = v___y_948_;
v___y_883_ = v___y_949_;
v___y_884_ = v___x_1005_;
v___y_885_ = v___x_1009_;
v___y_886_ = v___y_951_;
v___y_887_ = v___y_952_;
v___y_888_ = v___x_1011_;
v___y_889_ = v___y_954_;
v___y_890_ = v___y_955_;
v___y_891_ = v___x_983_;
v___y_892_ = v___y_957_;
v___y_893_ = v___y_959_;
v___y_894_ = v___y_958_;
v___y_895_ = v___y_962_;
v___y_896_ = v___y_963_;
v___y_897_ = v___x_1007_;
v___y_898_ = v___y_966_;
v___y_899_ = v___y_961_;
goto v___jp_881_;
}
else
{
lean_object* v_val_1012_; 
lean_dec(v___y_961_);
v_val_1012_ = lean_ctor_get(v___y_960_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v___y_960_, 1);
v___y_882_ = v___y_948_;
v___y_883_ = v___y_949_;
v___y_884_ = v___x_1005_;
v___y_885_ = v___x_1009_;
v___y_886_ = v___y_951_;
v___y_887_ = v___y_952_;
v___y_888_ = v___x_1011_;
v___y_889_ = v___y_954_;
v___y_890_ = v___y_955_;
v___y_891_ = v___x_983_;
v___y_892_ = v___y_957_;
v___y_893_ = v___y_959_;
v___y_894_ = v___y_958_;
v___y_895_ = v___y_962_;
v___y_896_ = v___y_963_;
v___y_897_ = v___x_1007_;
v___y_898_ = v___y_966_;
v___y_899_ = v_val_1012_;
goto v___jp_881_;
}
}
v___jp_1013_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; size_t v_sz_1042_; lean_object* v___x_1043_; size_t v_sz_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1032_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1033_ = lean_box(2);
lean_inc_n(v___y_1021_, 4);
v___x_1034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___y_1021_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
v___x_1035_ = lean_mk_empty_array_with_capacity(v___y_1022_);
v___x_1036_ = lean_array_push(v___x_1035_, v___y_1031_);
v___x_1037_ = lean_array_push(v___x_1036_, v___x_1034_);
v___x_1038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1033_);
lean_ctor_set(v___x_1038_, 1, v___y_1019_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
v___x_1039_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1018_);
lean_inc_ref_n(v___y_1023_, 6);
v___x_1040_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___y_1018_, v___x_1039_);
v___x_1041_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1042_ = lean_array_size(v___y_1020_);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1042_, v___y_1016_, v___y_1020_);
v_sz_1044_ = lean_array_size(v___x_1043_);
v___x_1045_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1044_, v___y_1016_, v___x_1043_);
lean_inc_ref(v___y_1027_);
v___x_1046_ = l_Array_append___redArg(v___y_1027_, v___x_1045_);
lean_dec_ref(v___x_1045_);
lean_inc_n(v___y_1025_, 14);
v___x_1047_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1047_, 0, v___y_1025_);
lean_ctor_set(v___x_1047_, 1, v___y_1021_);
lean_ctor_set(v___x_1047_, 2, v___x_1046_);
v___x_1048_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1014_, 2);
v___x_1049_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___y_1014_, v___x_1048_);
v___x_1050_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___y_1025_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1053_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___y_1014_, v___x_1052_);
v___x_1054_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1055_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___y_1025_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1057_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___x_1056_, v___x_1041_);
v___x_1058_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1059_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___y_1025_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = l_Lean_Syntax_node1(v___y_1025_, v___x_1057_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node1(v___y_1025_, v___y_1021_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node2(v___y_1025_, v___x_1053_, v___x_1055_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node2(v___y_1025_, v___x_1049_, v___x_1051_, v___x_1062_);
v___x_1064_ = l_Lean_Syntax_node1(v___y_1025_, v___y_1021_, v___x_1063_);
v___x_1065_ = l_Lean_Syntax_node2(v___y_1025_, v___x_1040_, v___x_1047_, v___x_1064_);
v___x_1066_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1067_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___y_1018_, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1069_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___y_1025_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1071_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1072_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1023_, v___x_1070_, v___x_1071_);
lean_inc_n(v___y_1017_, 3);
v___x_1073_ = l_Lean_Syntax_node2(v___y_1025_, v___x_1072_, v___y_1017_, v___y_1017_);
v___x_1074_ = l_Lean_Syntax_node4(v___y_1025_, v___x_1067_, v___x_1069_, v___y_1024_, v___x_1073_, v___y_1017_);
v___x_1075_ = l_Lean_Syntax_node5(v___y_1025_, v___y_1015_, v___y_1029_, v___x_1038_, v___x_1065_, v___x_1074_, v___y_1017_);
v___x_1076_ = l_Lean_Syntax_node2(v___y_1025_, v___y_1030_, v___y_1028_, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___y_1026_);
return v___x_1077_;
}
v___jp_1078_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_inc_ref_n(v___y_1096_, 2);
v___x_1100_ = l_Array_append___redArg(v___y_1096_, v___y_1099_);
lean_dec_ref(v___y_1099_);
lean_inc_n(v___y_1088_, 5);
lean_inc_n(v___y_1094_, 20);
v___x_1101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1101_, 0, v___y_1094_);
lean_ctor_set(v___x_1101_, 1, v___y_1088_);
lean_ctor_set(v___x_1101_, 2, v___x_1100_);
v___x_1102_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1080_, 2);
lean_inc_ref_n(v___y_1090_, 6);
v___x_1103_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___y_1080_, v___x_1102_);
v___x_1104_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1105_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___y_1094_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1107_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___y_1080_, v___x_1106_);
v___x_1108_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1109_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1110_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___x_1108_, v___x_1109_);
v___x_1111_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1112_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_1079_);
lean_inc(v___y_1089_);
v___x_1113_ = l_Lean_addMacroScope(v___y_1089_, v___x_1112_, v___y_1079_);
lean_inc_n(v___y_1085_, 2);
v___x_1114_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1114_, 0, v___y_1094_);
lean_ctor_set(v___x_1114_, 1, v___x_1111_);
lean_ctor_set(v___x_1114_, 2, v___x_1113_);
lean_ctor_set(v___x_1114_, 3, v___y_1085_);
v___x_1115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1115_, 0, v___y_1094_);
lean_ctor_set(v___x_1115_, 1, v___y_1088_);
lean_ctor_set(v___x_1115_, 2, v___y_1096_);
lean_inc_ref_n(v___x_1115_, 7);
lean_inc(v___x_1110_);
v___x_1116_ = l_Lean_Syntax_node2(v___y_1094_, v___x_1110_, v___x_1114_, v___x_1115_);
lean_inc(v___x_1107_);
v___x_1117_ = l_Lean_Syntax_node2(v___y_1094_, v___x_1107_, v___y_1082_, v___x_1116_);
v___x_1118_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___y_1094_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
lean_inc(v___y_1097_);
v___x_1120_ = l_Lean_Syntax_node1(v___y_1094_, v___y_1097_, v___x_1115_);
v___x_1121_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_1122_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_1123_ = l_Lean_addMacroScope(v___y_1089_, v___x_1122_, v___y_1079_);
v___x_1124_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1124_, 0, v___y_1094_);
lean_ctor_set(v___x_1124_, 1, v___x_1121_);
lean_ctor_set(v___x_1124_, 2, v___x_1123_);
lean_ctor_set(v___x_1124_, 3, v___y_1085_);
v___x_1125_ = l_Lean_Syntax_node2(v___y_1094_, v___x_1110_, v___x_1124_, v___x_1115_);
v___x_1126_ = l_Lean_Syntax_node2(v___y_1094_, v___x_1107_, v___x_1120_, v___x_1125_);
v___x_1127_ = l_Lean_Syntax_node3(v___y_1094_, v___y_1088_, v___x_1117_, v___x_1119_, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___y_1094_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node3(v___y_1094_, v___x_1103_, v___x_1105_, v___x_1127_, v___x_1129_);
v___x_1131_ = l_Lean_Syntax_node1(v___y_1094_, v___y_1088_, v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_1083_, 3);
v___x_1133_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___y_1083_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___y_1094_);
lean_ctor_set(v___x_1134_, 1, v___x_1132_);
v___x_1135_ = l_Lean_Syntax_node1(v___y_1094_, v___x_1133_, v___x_1134_);
v___x_1136_ = l_Lean_Syntax_node1(v___y_1094_, v___y_1088_, v___x_1135_);
v___x_1137_ = l_Lean_Syntax_node7(v___y_1094_, v___y_1086_, v___x_1101_, v___x_1131_, v___x_1136_, v___x_1115_, v___x_1115_, v___x_1115_, v___x_1115_);
v___x_1138_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1139_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___y_1083_, v___x_1138_);
v___x_1140_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___y_1094_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1143_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1090_, v___y_1083_, v___x_1142_);
if (lean_obj_tag(v___y_1092_) == 0)
{
v___y_1014_ = v___y_1080_;
v___y_1015_ = v___x_1139_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___x_1115_;
v___y_1018_ = v___y_1083_;
v___y_1019_ = v___x_1143_;
v___y_1020_ = v___y_1084_;
v___y_1021_ = v___y_1088_;
v___y_1022_ = v___y_1087_;
v___y_1023_ = v___y_1090_;
v___y_1024_ = v___y_1091_;
v___y_1025_ = v___y_1094_;
v___y_1026_ = v___y_1095_;
v___y_1027_ = v___y_1096_;
v___y_1028_ = v___x_1137_;
v___y_1029_ = v___x_1141_;
v___y_1030_ = v___y_1098_;
v___y_1031_ = v___y_1093_;
goto v___jp_1013_;
}
else
{
lean_object* v_val_1144_; 
lean_dec(v___y_1093_);
v_val_1144_ = lean_ctor_get(v___y_1092_, 0);
lean_inc(v_val_1144_);
lean_dec_ref_known(v___y_1092_, 1);
v___y_1014_ = v___y_1080_;
v___y_1015_ = v___x_1139_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___x_1115_;
v___y_1018_ = v___y_1083_;
v___y_1019_ = v___x_1143_;
v___y_1020_ = v___y_1084_;
v___y_1021_ = v___y_1088_;
v___y_1022_ = v___y_1087_;
v___y_1023_ = v___y_1090_;
v___y_1024_ = v___y_1091_;
v___y_1025_ = v___y_1094_;
v___y_1026_ = v___y_1095_;
v___y_1027_ = v___y_1096_;
v___y_1028_ = v___x_1137_;
v___y_1029_ = v___x_1141_;
v___y_1030_ = v___y_1098_;
v___y_1031_ = v_val_1144_;
goto v___jp_1013_;
}
}
v___jp_1145_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; lean_object* v___x_1175_; size_t v_sz_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1164_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1165_ = lean_box(2);
lean_inc_n(v___y_1161_, 4);
v___x_1166_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___y_1161_);
lean_ctor_set(v___x_1166_, 2, v___x_1164_);
v___x_1167_ = lean_mk_empty_array_with_capacity(v___y_1154_);
v___x_1168_ = lean_array_push(v___x_1167_, v___y_1163_);
v___x_1169_ = lean_array_push(v___x_1168_, v___x_1166_);
v___x_1170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1165_);
lean_ctor_set(v___x_1170_, 1, v___y_1156_);
lean_ctor_set(v___x_1170_, 2, v___x_1169_);
v___x_1171_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1151_);
lean_inc_ref_n(v___y_1155_, 6);
v___x_1172_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___y_1151_, v___x_1171_);
v___x_1173_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1174_ = lean_array_size(v___y_1152_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1174_, v___y_1148_, v___y_1152_);
v_sz_1176_ = lean_array_size(v___x_1175_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1176_, v___y_1148_, v___x_1175_);
lean_inc_ref(v___y_1158_);
v___x_1178_ = l_Array_append___redArg(v___y_1158_, v___x_1177_);
lean_dec_ref(v___x_1177_);
lean_inc_n(v___y_1160_, 14);
v___x_1179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1160_);
lean_ctor_set(v___x_1179_, 1, v___y_1161_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1147_, 2);
v___x_1181_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___y_1147_, v___x_1180_);
v___x_1182_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1160_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1185_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___y_1147_, v___x_1184_);
v___x_1186_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___y_1160_);
lean_ctor_set(v___x_1187_, 1, v___x_1186_);
v___x_1188_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1189_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___x_1188_, v___x_1173_);
v___x_1190_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___y_1160_);
lean_ctor_set(v___x_1191_, 1, v___x_1190_);
v___x_1192_ = l_Lean_Syntax_node1(v___y_1160_, v___x_1189_, v___x_1191_);
v___x_1193_ = l_Lean_Syntax_node1(v___y_1160_, v___y_1161_, v___x_1192_);
v___x_1194_ = l_Lean_Syntax_node2(v___y_1160_, v___x_1185_, v___x_1187_, v___x_1193_);
v___x_1195_ = l_Lean_Syntax_node2(v___y_1160_, v___x_1181_, v___x_1183_, v___x_1194_);
v___x_1196_ = l_Lean_Syntax_node1(v___y_1160_, v___y_1161_, v___x_1195_);
v___x_1197_ = l_Lean_Syntax_node2(v___y_1160_, v___x_1172_, v___x_1179_, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1199_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___y_1151_, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___y_1160_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
v___x_1202_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1203_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1204_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1155_, v___x_1202_, v___x_1203_);
lean_inc_n(v___y_1149_, 3);
v___x_1205_ = l_Lean_Syntax_node2(v___y_1160_, v___x_1204_, v___y_1149_, v___y_1149_);
v___x_1206_ = l_Lean_Syntax_node4(v___y_1160_, v___x_1199_, v___x_1201_, v___y_1157_, v___x_1205_, v___y_1149_);
v___x_1207_ = l_Lean_Syntax_node5(v___y_1160_, v___y_1159_, v___y_1162_, v___x_1170_, v___x_1197_, v___x_1206_, v___y_1149_);
v___x_1208_ = l_Lean_Syntax_node2(v___y_1160_, v___y_1150_, v___y_1153_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___y_1146_);
return v___x_1209_;
}
v___jp_1210_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
lean_inc_ref_n(v___y_1226_, 2);
v___x_1232_ = l_Array_append___redArg(v___y_1226_, v___y_1231_);
lean_dec_ref(v___y_1231_);
lean_inc_n(v___y_1229_, 5);
lean_inc_n(v___y_1227_, 20);
v___x_1233_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1233_, 0, v___y_1227_);
lean_ctor_set(v___x_1233_, 1, v___y_1229_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1212_, 2);
lean_inc_ref_n(v___y_1222_, 6);
v___x_1235_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___y_1212_, v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1227_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1239_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___y_1212_, v___x_1238_);
v___x_1240_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1241_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1242_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___x_1240_, v___x_1241_);
v___x_1243_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1244_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_1211_);
lean_inc(v___y_1221_);
v___x_1245_ = l_Lean_addMacroScope(v___y_1221_, v___x_1244_, v___y_1211_);
lean_inc_n(v___y_1219_, 2);
v___x_1246_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1246_, 0, v___y_1227_);
lean_ctor_set(v___x_1246_, 1, v___x_1243_);
lean_ctor_set(v___x_1246_, 2, v___x_1245_);
lean_ctor_set(v___x_1246_, 3, v___y_1219_);
v___x_1247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1247_, 0, v___y_1227_);
lean_ctor_set(v___x_1247_, 1, v___y_1229_);
lean_ctor_set(v___x_1247_, 2, v___y_1226_);
lean_inc_ref_n(v___x_1247_, 7);
lean_inc(v___x_1242_);
v___x_1248_ = l_Lean_Syntax_node2(v___y_1227_, v___x_1242_, v___x_1246_, v___x_1247_);
lean_inc(v___x_1239_);
v___x_1249_ = l_Lean_Syntax_node2(v___y_1227_, v___x_1239_, v___y_1215_, v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1251_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1251_, 0, v___y_1227_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
lean_inc(v___y_1230_);
v___x_1252_ = l_Lean_Syntax_node1(v___y_1227_, v___y_1230_, v___x_1247_);
v___x_1253_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_1254_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_1255_ = l_Lean_addMacroScope(v___y_1221_, v___x_1254_, v___y_1211_);
v___x_1256_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1256_, 0, v___y_1227_);
lean_ctor_set(v___x_1256_, 1, v___x_1253_);
lean_ctor_set(v___x_1256_, 2, v___x_1255_);
lean_ctor_set(v___x_1256_, 3, v___y_1219_);
v___x_1257_ = l_Lean_Syntax_node2(v___y_1227_, v___x_1242_, v___x_1256_, v___x_1247_);
v___x_1258_ = l_Lean_Syntax_node2(v___y_1227_, v___x_1239_, v___x_1252_, v___x_1257_);
v___x_1259_ = l_Lean_Syntax_node3(v___y_1227_, v___y_1229_, v___x_1249_, v___x_1251_, v___x_1258_);
v___x_1260_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___y_1227_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_Syntax_node3(v___y_1227_, v___x_1235_, v___x_1237_, v___x_1259_, v___x_1261_);
v___x_1263_ = l_Lean_Syntax_node1(v___y_1227_, v___y_1229_, v___x_1262_);
v___x_1264_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_1218_, 3);
v___x_1265_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___y_1218_, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1227_);
lean_ctor_set(v___x_1266_, 1, v___x_1264_);
v___x_1267_ = l_Lean_Syntax_node1(v___y_1227_, v___x_1265_, v___x_1266_);
v___x_1268_ = l_Lean_Syntax_node1(v___y_1227_, v___y_1229_, v___x_1267_);
v___x_1269_ = l_Lean_Syntax_node7(v___y_1227_, v___y_1228_, v___x_1233_, v___x_1263_, v___x_1268_, v___x_1247_, v___x_1247_, v___x_1247_, v___x_1247_);
v___x_1270_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1271_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___y_1218_, v___x_1270_);
v___x_1272_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1273_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___y_1227_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1275_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1222_, v___y_1218_, v___x_1274_);
if (lean_obj_tag(v___y_1224_) == 0)
{
v___y_1146_ = v___y_1213_;
v___y_1147_ = v___y_1212_;
v___y_1148_ = v___y_1214_;
v___y_1149_ = v___x_1247_;
v___y_1150_ = v___y_1217_;
v___y_1151_ = v___y_1218_;
v___y_1152_ = v___y_1216_;
v___y_1153_ = v___x_1269_;
v___y_1154_ = v___y_1220_;
v___y_1155_ = v___y_1222_;
v___y_1156_ = v___x_1275_;
v___y_1157_ = v___y_1223_;
v___y_1158_ = v___y_1226_;
v___y_1159_ = v___x_1271_;
v___y_1160_ = v___y_1227_;
v___y_1161_ = v___y_1229_;
v___y_1162_ = v___x_1273_;
v___y_1163_ = v___y_1225_;
goto v___jp_1145_;
}
else
{
lean_object* v_val_1276_; 
lean_dec(v___y_1225_);
v_val_1276_ = lean_ctor_get(v___y_1224_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___y_1224_, 1);
v___y_1146_ = v___y_1213_;
v___y_1147_ = v___y_1212_;
v___y_1148_ = v___y_1214_;
v___y_1149_ = v___x_1247_;
v___y_1150_ = v___y_1217_;
v___y_1151_ = v___y_1218_;
v___y_1152_ = v___y_1216_;
v___y_1153_ = v___x_1269_;
v___y_1154_ = v___y_1220_;
v___y_1155_ = v___y_1222_;
v___y_1156_ = v___x_1275_;
v___y_1157_ = v___y_1223_;
v___y_1158_ = v___y_1226_;
v___y_1159_ = v___x_1271_;
v___y_1160_ = v___y_1227_;
v___y_1161_ = v___y_1229_;
v___y_1162_ = v___x_1273_;
v___y_1163_ = v_val_1276_;
goto v___jp_1145_;
}
}
v___jp_1277_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; size_t v_sz_1306_; lean_object* v___x_1307_; size_t v_sz_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1296_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1297_ = lean_box(2);
lean_inc_n(v___y_1288_, 4);
v___x_1298_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
lean_ctor_set(v___x_1298_, 1, v___y_1288_);
lean_ctor_set(v___x_1298_, 2, v___x_1296_);
v___x_1299_ = lean_mk_empty_array_with_capacity(v___y_1289_);
v___x_1300_ = lean_array_push(v___x_1299_, v___y_1295_);
v___x_1301_ = lean_array_push(v___x_1300_, v___x_1298_);
v___x_1302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1297_);
lean_ctor_set(v___x_1302_, 1, v___y_1283_);
lean_ctor_set(v___x_1302_, 2, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1290_);
lean_inc_ref_n(v___y_1291_, 6);
v___x_1304_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___y_1290_, v___x_1303_);
v___x_1305_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1306_ = lean_array_size(v___y_1287_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1306_, v___y_1280_, v___y_1287_);
v_sz_1308_ = lean_array_size(v___x_1307_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1308_, v___y_1280_, v___x_1307_);
lean_inc_ref(v___y_1284_);
v___x_1310_ = l_Array_append___redArg(v___y_1284_, v___x_1309_);
lean_dec_ref(v___x_1309_);
lean_inc_n(v___y_1293_, 14);
v___x_1311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1311_, 0, v___y_1293_);
lean_ctor_set(v___x_1311_, 1, v___y_1288_);
lean_ctor_set(v___x_1311_, 2, v___x_1310_);
v___x_1312_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1278_, 2);
v___x_1313_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___y_1278_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___y_1293_);
lean_ctor_set(v___x_1315_, 1, v___x_1314_);
v___x_1316_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1317_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___y_1278_, v___x_1316_);
v___x_1318_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1319_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___y_1293_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1321_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___x_1320_, v___x_1305_);
v___x_1322_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___y_1293_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_Syntax_node1(v___y_1293_, v___x_1321_, v___x_1323_);
v___x_1325_ = l_Lean_Syntax_node1(v___y_1293_, v___y_1288_, v___x_1324_);
v___x_1326_ = l_Lean_Syntax_node2(v___y_1293_, v___x_1317_, v___x_1319_, v___x_1325_);
v___x_1327_ = l_Lean_Syntax_node2(v___y_1293_, v___x_1313_, v___x_1315_, v___x_1326_);
v___x_1328_ = l_Lean_Syntax_node1(v___y_1293_, v___y_1288_, v___x_1327_);
v___x_1329_ = l_Lean_Syntax_node2(v___y_1293_, v___x_1304_, v___x_1311_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1331_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___y_1290_, v___x_1330_);
v___x_1332_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1333_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___y_1293_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1335_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1336_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1291_, v___x_1334_, v___x_1335_);
lean_inc_n(v___y_1282_, 3);
v___x_1337_ = l_Lean_Syntax_node2(v___y_1293_, v___x_1336_, v___y_1282_, v___y_1282_);
v___x_1338_ = l_Lean_Syntax_node4(v___y_1293_, v___x_1331_, v___x_1333_, v___y_1292_, v___x_1337_, v___y_1282_);
v___x_1339_ = l_Lean_Syntax_node5(v___y_1293_, v___y_1285_, v___y_1294_, v___x_1302_, v___x_1329_, v___x_1338_, v___y_1282_);
v___x_1340_ = l_Lean_Syntax_node2(v___y_1293_, v___y_1279_, v___y_1281_, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v___y_1286_);
return v___x_1341_;
}
v___jp_1342_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
lean_inc_ref_n(v___y_1348_, 2);
v___x_1363_ = l_Array_append___redArg(v___y_1348_, v___y_1362_);
lean_dec_ref(v___y_1362_);
lean_inc_n(v___y_1353_, 5);
lean_inc_n(v___y_1360_, 15);
v___x_1364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1364_, 0, v___y_1360_);
lean_ctor_set(v___x_1364_, 1, v___y_1353_);
lean_ctor_set(v___x_1364_, 2, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1344_, 2);
lean_inc_ref_n(v___y_1356_, 6);
v___x_1366_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___y_1344_, v___x_1365_);
v___x_1367_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1368_, 0, v___y_1360_);
lean_ctor_set(v___x_1368_, 1, v___x_1367_);
v___x_1369_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1370_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___y_1344_, v___x_1369_);
v___x_1371_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1372_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1373_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___x_1371_, v___x_1372_);
v___x_1374_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1375_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
v___x_1376_ = l_Lean_addMacroScope(v___y_1354_, v___x_1375_, v___y_1343_);
lean_inc(v___y_1351_);
v___x_1377_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1377_, 0, v___y_1360_);
lean_ctor_set(v___x_1377_, 1, v___x_1374_);
lean_ctor_set(v___x_1377_, 2, v___x_1376_);
lean_ctor_set(v___x_1377_, 3, v___y_1351_);
v___x_1378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1378_, 0, v___y_1360_);
lean_ctor_set(v___x_1378_, 1, v___y_1353_);
lean_ctor_set(v___x_1378_, 2, v___y_1348_);
lean_inc_ref_n(v___x_1378_, 5);
v___x_1379_ = l_Lean_Syntax_node2(v___y_1360_, v___x_1373_, v___x_1377_, v___x_1378_);
v___x_1380_ = l_Lean_Syntax_node2(v___y_1360_, v___x_1370_, v___y_1347_, v___x_1379_);
v___x_1381_ = l_Lean_Syntax_node1(v___y_1360_, v___y_1353_, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1383_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___y_1360_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
v___x_1384_ = l_Lean_Syntax_node3(v___y_1360_, v___x_1366_, v___x_1368_, v___x_1381_, v___x_1383_);
v___x_1385_ = l_Lean_Syntax_node1(v___y_1360_, v___y_1353_, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26));
lean_inc_ref_n(v___y_1355_, 3);
v___x_1387_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___y_1355_, v___x_1386_);
v___x_1388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___y_1360_);
lean_ctor_set(v___x_1388_, 1, v___x_1386_);
v___x_1389_ = l_Lean_Syntax_node1(v___y_1360_, v___x_1387_, v___x_1388_);
v___x_1390_ = l_Lean_Syntax_node1(v___y_1360_, v___y_1353_, v___x_1389_);
v___x_1391_ = l_Lean_Syntax_node7(v___y_1360_, v___y_1361_, v___x_1364_, v___x_1385_, v___x_1390_, v___x_1378_, v___x_1378_, v___x_1378_, v___x_1378_);
v___x_1392_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1393_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___y_1355_, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1395_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___y_1360_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
v___x_1396_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1397_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1356_, v___y_1355_, v___x_1396_);
if (lean_obj_tag(v___y_1358_) == 0)
{
v___y_1278_ = v___y_1344_;
v___y_1279_ = v___y_1345_;
v___y_1280_ = v___y_1346_;
v___y_1281_ = v___x_1391_;
v___y_1282_ = v___x_1378_;
v___y_1283_ = v___x_1397_;
v___y_1284_ = v___y_1348_;
v___y_1285_ = v___x_1393_;
v___y_1286_ = v___y_1349_;
v___y_1287_ = v___y_1350_;
v___y_1288_ = v___y_1353_;
v___y_1289_ = v___y_1352_;
v___y_1290_ = v___y_1355_;
v___y_1291_ = v___y_1356_;
v___y_1292_ = v___y_1357_;
v___y_1293_ = v___y_1360_;
v___y_1294_ = v___x_1395_;
v___y_1295_ = v___y_1359_;
goto v___jp_1277_;
}
else
{
lean_object* v_val_1398_; 
lean_dec(v___y_1359_);
v_val_1398_ = lean_ctor_get(v___y_1358_, 0);
lean_inc(v_val_1398_);
lean_dec_ref_known(v___y_1358_, 1);
v___y_1278_ = v___y_1344_;
v___y_1279_ = v___y_1345_;
v___y_1280_ = v___y_1346_;
v___y_1281_ = v___x_1391_;
v___y_1282_ = v___x_1378_;
v___y_1283_ = v___x_1397_;
v___y_1284_ = v___y_1348_;
v___y_1285_ = v___x_1393_;
v___y_1286_ = v___y_1349_;
v___y_1287_ = v___y_1350_;
v___y_1288_ = v___y_1353_;
v___y_1289_ = v___y_1352_;
v___y_1290_ = v___y_1355_;
v___y_1291_ = v___y_1356_;
v___y_1292_ = v___y_1357_;
v___y_1293_ = v___y_1360_;
v___y_1294_ = v___x_1395_;
v___y_1295_ = v_val_1398_;
goto v___jp_1277_;
}
}
v___jp_1399_:
{
lean_object* v_quotContext_1417_; lean_object* v_currMacroScope_1418_; lean_object* v_ref_1419_; lean_object* v___x_1420_; lean_object* v_a_1421_; lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1513_; 
v_quotContext_1417_ = lean_ctor_get(v___y_1415_, 1);
v_currMacroScope_1418_ = lean_ctor_get(v___y_1415_, 2);
v_ref_1419_ = lean_ctor_get(v___y_1415_, 5);
v___x_1420_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v___y_1412_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_a_1422_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1424_ = v___x_1420_;
v_isShared_1425_ = v_isSharedCheck_1513_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1513_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_1427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v_a_1421_);
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 2);
lean_ctor_set(v___x_1424_, 1, v___x_1427_);
v___x_1429_ = v___x_1424_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1421_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; size_t v_sz_1433_; lean_object* v___x_1434_; 
v___x_1430_ = l_Lean_Syntax_node3(v_a_1421_, v___x_1426_, v___y_1406_, v___x_1429_, v___y_1401_);
v___x_1431_ = l_Array_zip___redArg(v___y_1405_, v___y_1407_);
lean_dec_ref(v___y_1407_);
lean_dec_ref(v___y_1405_);
v___x_1432_ = l_Array_reverse___redArg(v___x_1431_);
v_sz_1433_ = lean_array_size(v___x_1432_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v___x_1432_, v_sz_1433_, v___y_1403_, v___x_1430_, v___y_1415_, v_a_1422_);
lean_dec_ref(v___x_1432_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_a_1436_; lean_object* v___x_1437_; lean_object* v_a_1438_; lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
v_a_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___x_1434_, 2);
v___x_1437_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v_a_1436_);
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
v_a_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1437_);
v___x_1440_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28);
v___x_1441_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29));
lean_inc(v_currMacroScope_1418_);
lean_inc(v_quotContext_1417_);
v___x_1442_ = l_Lean_addMacroScope(v_quotContext_1417_, v___x_1441_, v_currMacroScope_1418_);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1438_);
lean_ctor_set(v___x_1444_, 1, v___x_1440_);
lean_ctor_set(v___x_1444_, 2, v___x_1442_);
lean_ctor_set(v___x_1444_, 3, v___x_1443_);
if (v___y_1410_ == 0)
{
lean_object* v___x_1445_; lean_object* v_a_1446_; lean_object* v_a_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1445_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v_a_1439_);
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1446_);
v_a_1447_ = lean_ctor_get(v___x_1445_, 1);
lean_inc(v_a_1447_);
lean_dec_ref(v___x_1445_);
v___x_1448_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1449_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1413_, 2);
v___x_1450_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1448_, v___x_1449_);
v___x_1451_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1452_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1448_, v___x_1451_);
v___x_1453_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1454_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1400_) == 1)
{
lean_object* v_val_1455_; lean_object* v___x_1456_; 
v_val_1455_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_val_1455_);
lean_dec_ref_known(v___y_1400_, 1);
v___x_1456_ = l_Array_mkArray1___redArg(v_val_1455_);
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_947_ = v_currMacroScope_1418_;
v___y_948_ = v___y_1402_;
v___y_949_ = v___y_1403_;
v___y_950_ = v___y_1404_;
v___y_951_ = v___x_1453_;
v___y_952_ = v___y_1408_;
v___y_953_ = v___x_1443_;
v___y_954_ = v___y_1411_;
v___y_955_ = v_a_1446_;
v___y_956_ = v_quotContext_1417_;
v___y_957_ = v___y_1413_;
v___y_958_ = v_a_1435_;
v___y_959_ = v___x_1450_;
v___y_960_ = v___y_1416_;
v___y_961_ = v___x_1444_;
v___y_962_ = v___x_1454_;
v___y_963_ = v_a_1447_;
v___y_964_ = v___y_1414_;
v___y_965_ = v___x_1452_;
v___y_966_ = v___x_1448_;
v___y_967_ = v___x_1456_;
goto v___jp_946_;
}
else
{
lean_object* v___x_1457_; 
lean_dec(v___y_1400_);
v___x_1457_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_947_ = v_currMacroScope_1418_;
v___y_948_ = v___y_1402_;
v___y_949_ = v___y_1403_;
v___y_950_ = v___y_1404_;
v___y_951_ = v___x_1453_;
v___y_952_ = v___y_1408_;
v___y_953_ = v___x_1443_;
v___y_954_ = v___y_1411_;
v___y_955_ = v_a_1446_;
v___y_956_ = v_quotContext_1417_;
v___y_957_ = v___y_1413_;
v___y_958_ = v_a_1435_;
v___y_959_ = v___x_1450_;
v___y_960_ = v___y_1416_;
v___y_961_ = v___x_1444_;
v___y_962_ = v___x_1454_;
v___y_963_ = v_a_1447_;
v___y_964_ = v___y_1414_;
v___y_965_ = v___x_1452_;
v___y_966_ = v___x_1448_;
v___y_967_ = v___x_1457_;
goto v___jp_946_;
}
}
else
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = l_Lean_Syntax_getArg(v___y_1404_, v___x_880_);
lean_inc(v___x_1458_);
v___x_1459_ = l_Lean_Syntax_matchesNull(v___x_1458_, v___y_1409_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v_a_1461_; lean_object* v_a_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1458_);
v___x_1460_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v_a_1439_);
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
v_a_1462_ = lean_ctor_get(v___x_1460_, 1);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1460_);
v___x_1463_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1464_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1413_, 2);
v___x_1465_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1463_, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1467_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1463_, v___x_1466_);
v___x_1468_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1469_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1400_) == 1)
{
lean_object* v_val_1470_; lean_object* v___x_1471_; 
v_val_1470_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_val_1470_);
lean_dec_ref_known(v___y_1400_, 1);
v___x_1471_ = l_Array_mkArray1___redArg(v_val_1470_);
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1079_ = v_currMacroScope_1418_;
v___y_1080_ = v___y_1402_;
v___y_1081_ = v___y_1403_;
v___y_1082_ = v___y_1404_;
v___y_1083_ = v___x_1463_;
v___y_1084_ = v___y_1408_;
v___y_1085_ = v___x_1443_;
v___y_1086_ = v___x_1467_;
v___y_1087_ = v___y_1411_;
v___y_1088_ = v___x_1468_;
v___y_1089_ = v_quotContext_1417_;
v___y_1090_ = v___y_1413_;
v___y_1091_ = v_a_1435_;
v___y_1092_ = v___y_1416_;
v___y_1093_ = v___x_1444_;
v___y_1094_ = v_a_1461_;
v___y_1095_ = v_a_1462_;
v___y_1096_ = v___x_1469_;
v___y_1097_ = v___y_1414_;
v___y_1098_ = v___x_1465_;
v___y_1099_ = v___x_1471_;
goto v___jp_1078_;
}
else
{
lean_object* v___x_1472_; 
lean_dec(v___y_1400_);
v___x_1472_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1079_ = v_currMacroScope_1418_;
v___y_1080_ = v___y_1402_;
v___y_1081_ = v___y_1403_;
v___y_1082_ = v___y_1404_;
v___y_1083_ = v___x_1463_;
v___y_1084_ = v___y_1408_;
v___y_1085_ = v___x_1443_;
v___y_1086_ = v___x_1467_;
v___y_1087_ = v___y_1411_;
v___y_1088_ = v___x_1468_;
v___y_1089_ = v_quotContext_1417_;
v___y_1090_ = v___y_1413_;
v___y_1091_ = v_a_1435_;
v___y_1092_ = v___y_1416_;
v___y_1093_ = v___x_1444_;
v___y_1094_ = v_a_1461_;
v___y_1095_ = v_a_1462_;
v___y_1096_ = v___x_1469_;
v___y_1097_ = v___y_1414_;
v___y_1098_ = v___x_1465_;
v___y_1099_ = v___x_1472_;
goto v___jp_1078_;
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v___x_1473_ = l_Lean_Syntax_getArg(v___x_1458_, v___x_880_);
lean_dec(v___x_1458_);
v___x_1474_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34));
lean_inc_ref(v___y_1402_);
lean_inc_ref(v___y_1413_);
v___x_1475_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___y_1402_, v___x_1474_);
v___x_1476_ = l_Lean_Syntax_isOfKind(v___x_1473_, v___x_1475_);
lean_dec(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v_a_1478_; lean_object* v_a_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1477_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v_a_1439_);
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
v_a_1479_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1477_);
v___x_1480_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1481_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1413_, 2);
v___x_1482_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1480_, v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1484_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1480_, v___x_1483_);
v___x_1485_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1486_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1400_) == 1)
{
lean_object* v_val_1487_; lean_object* v___x_1488_; 
v_val_1487_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v___y_1400_, 1);
v___x_1488_ = l_Array_mkArray1___redArg(v_val_1487_);
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1211_ = v_currMacroScope_1418_;
v___y_1212_ = v___y_1402_;
v___y_1213_ = v_a_1479_;
v___y_1214_ = v___y_1403_;
v___y_1215_ = v___y_1404_;
v___y_1216_ = v___y_1408_;
v___y_1217_ = v___x_1482_;
v___y_1218_ = v___x_1480_;
v___y_1219_ = v___x_1443_;
v___y_1220_ = v___y_1411_;
v___y_1221_ = v_quotContext_1417_;
v___y_1222_ = v___y_1413_;
v___y_1223_ = v_a_1435_;
v___y_1224_ = v___y_1416_;
v___y_1225_ = v___x_1444_;
v___y_1226_ = v___x_1486_;
v___y_1227_ = v_a_1478_;
v___y_1228_ = v___x_1484_;
v___y_1229_ = v___x_1485_;
v___y_1230_ = v___y_1414_;
v___y_1231_ = v___x_1488_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1489_; 
lean_dec(v___y_1400_);
v___x_1489_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1211_ = v_currMacroScope_1418_;
v___y_1212_ = v___y_1402_;
v___y_1213_ = v_a_1479_;
v___y_1214_ = v___y_1403_;
v___y_1215_ = v___y_1404_;
v___y_1216_ = v___y_1408_;
v___y_1217_ = v___x_1482_;
v___y_1218_ = v___x_1480_;
v___y_1219_ = v___x_1443_;
v___y_1220_ = v___y_1411_;
v___y_1221_ = v_quotContext_1417_;
v___y_1222_ = v___y_1413_;
v___y_1223_ = v_a_1435_;
v___y_1224_ = v___y_1416_;
v___y_1225_ = v___x_1444_;
v___y_1226_ = v___x_1486_;
v___y_1227_ = v_a_1478_;
v___y_1228_ = v___x_1484_;
v___y_1229_ = v___x_1485_;
v___y_1230_ = v___y_1414_;
v___y_1231_ = v___x_1489_;
goto v___jp_1210_;
}
}
else
{
lean_object* v___x_1490_; lean_object* v_a_1491_; lean_object* v_a_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1490_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1419_, v___y_1415_, v_a_1439_);
v_a_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_a_1491_);
v_a_1492_ = lean_ctor_get(v___x_1490_, 1);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1490_);
v___x_1493_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1494_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1413_, 2);
v___x_1495_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1493_, v___x_1494_);
v___x_1496_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1497_ = l_Lean_Name_mkStr4(v___x_875_, v___y_1413_, v___x_1493_, v___x_1496_);
v___x_1498_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1499_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1400_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; 
v_val_1500_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___y_1400_, 1);
v___x_1501_ = l_Array_mkArray1___redArg(v_val_1500_);
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1343_ = v_currMacroScope_1418_;
v___y_1344_ = v___y_1402_;
v___y_1345_ = v___x_1495_;
v___y_1346_ = v___y_1403_;
v___y_1347_ = v___y_1404_;
v___y_1348_ = v___x_1499_;
v___y_1349_ = v_a_1492_;
v___y_1350_ = v___y_1408_;
v___y_1351_ = v___x_1443_;
v___y_1352_ = v___y_1411_;
v___y_1353_ = v___x_1498_;
v___y_1354_ = v_quotContext_1417_;
v___y_1355_ = v___x_1493_;
v___y_1356_ = v___y_1413_;
v___y_1357_ = v_a_1435_;
v___y_1358_ = v___y_1416_;
v___y_1359_ = v___x_1444_;
v___y_1360_ = v_a_1491_;
v___y_1361_ = v___x_1497_;
v___y_1362_ = v___x_1501_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1502_; 
lean_dec(v___y_1400_);
v___x_1502_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_quotContext_1417_);
lean_inc(v_currMacroScope_1418_);
v___y_1343_ = v_currMacroScope_1418_;
v___y_1344_ = v___y_1402_;
v___y_1345_ = v___x_1495_;
v___y_1346_ = v___y_1403_;
v___y_1347_ = v___y_1404_;
v___y_1348_ = v___x_1499_;
v___y_1349_ = v_a_1492_;
v___y_1350_ = v___y_1408_;
v___y_1351_ = v___x_1443_;
v___y_1352_ = v___y_1411_;
v___y_1353_ = v___x_1498_;
v___y_1354_ = v_quotContext_1417_;
v___y_1355_ = v___x_1493_;
v___y_1356_ = v___y_1413_;
v___y_1357_ = v_a_1435_;
v___y_1358_ = v___y_1416_;
v___y_1359_ = v___x_1444_;
v___y_1360_ = v_a_1491_;
v___y_1361_ = v___x_1497_;
v___y_1362_ = v___x_1502_;
goto v___jp_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1404_);
lean_dec(v___y_1400_);
v_a_1503_ = lean_ctor_get(v___x_1434_, 0);
v_a_1504_ = lean_ctor_get(v___x_1434_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1434_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_inc(v_a_1503_);
lean_dec(v___x_1434_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1503_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = l_Lean_Syntax_getArg(v_x_872_, v___x_1518_);
v___x_1520_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_1521_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v___x_1522_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35));
lean_inc(v___x_1519_);
v___x_1523_ = l_Lean_Syntax_isOfKind(v___x_1519_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v___x_1519_);
lean_dec(v_doc_x3f_1515_);
lean_dec(v_x_872_);
v___x_1524_ = lean_box(1);
v___x_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___y_1517_);
return v___x_1525_;
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; size_t v_sz_1529_; size_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1526_ = lean_unsigned_to_nat(6u);
v___x_1527_ = l_Lean_Syntax_getArg(v_x_872_, v___x_1526_);
v___x_1528_ = l_Lean_Syntax_getArgs(v___x_1527_);
lean_dec(v___x_1527_);
v_sz_1529_ = lean_array_size(v___x_1528_);
v___x_1530_ = ((size_t)0ULL);
v___x_1531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_1529_, v___x_1530_, v___x_1528_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
lean_dec(v___x_1519_);
lean_dec(v_doc_x3f_1515_);
lean_dec(v_x_872_);
v___x_1532_ = lean_box(1);
v___x_1533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___y_1517_);
return v___x_1533_;
}
else
{
lean_object* v_val_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_val_1534_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1535_ = lean_unsigned_to_nat(8u);
v___x_1536_ = l_Lean_Syntax_getArg(v_x_872_, v___x_1535_);
v___x_1537_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_1536_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v___x_1536_);
lean_dec(v_val_1534_);
lean_dec(v___x_1519_);
lean_dec(v_doc_x3f_1515_);
lean_dec(v_x_872_);
v___x_1539_ = lean_box(1);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___y_1517_);
return v___x_1540_;
}
else
{
size_t v_sz_1541_; lean_object* v___x_1542_; lean_object* v_cs_u2082_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_cs_u2081_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_bs_1551_; lean_object* v___x_1552_; 
v_sz_1541_ = lean_array_size(v_val_1534_);
v___x_1542_ = lean_unsigned_to_nat(2u);
lean_inc(v_val_1534_);
v_cs_u2082_1543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_1541_, v___x_1530_, v_val_1534_);
v___x_1544_ = lean_unsigned_to_nat(3u);
v___x_1545_ = l_Lean_Syntax_getArg(v_x_872_, v___x_1544_);
v___x_1546_ = lean_unsigned_to_nat(4u);
v___x_1547_ = l_Lean_Syntax_getArg(v_x_872_, v___x_1546_);
lean_dec(v_x_872_);
v_cs_u2081_1548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_1541_, v___x_1530_, v_val_1534_);
v___x_1549_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_880_);
v___x_1550_ = l_Lean_Syntax_getArg(v___x_1536_, v___x_1542_);
lean_dec(v___x_1536_);
v_bs_1551_ = l_Lean_Syntax_getArgs(v___x_1547_);
lean_dec(v___x_1547_);
v___x_1552_ = l_Lean_Syntax_getOptional_x3f(v___x_1545_);
lean_dec(v___x_1545_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_box(0);
v___y_1400_ = v_doc_x3f_1515_;
v___y_1401_ = v___x_1550_;
v___y_1402_ = v___x_1521_;
v___y_1403_ = v___x_1530_;
v___y_1404_ = v___x_1519_;
v___y_1405_ = v_cs_u2081_1548_;
v___y_1406_ = v___x_1549_;
v___y_1407_ = v_cs_u2082_1543_;
v___y_1408_ = v_bs_1551_;
v___y_1409_ = v___x_1518_;
v___y_1410_ = v___x_1523_;
v___y_1411_ = v___x_1542_;
v___y_1412_ = v___y_1517_;
v___y_1413_ = v___x_1520_;
v___y_1414_ = v___x_1522_;
v___y_1415_ = v___y_1516_;
v___y_1416_ = v___x_1553_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
v_val_1554_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1552_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_val_1554_);
lean_dec(v___x_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_val_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
v___y_1400_ = v_doc_x3f_1515_;
v___y_1401_ = v___x_1550_;
v___y_1402_ = v___x_1521_;
v___y_1403_ = v___x_1530_;
v___y_1404_ = v___x_1519_;
v___y_1405_ = v_cs_u2081_1548_;
v___y_1406_ = v___x_1549_;
v___y_1407_ = v_cs_u2082_1543_;
v___y_1408_ = v_bs_1551_;
v___y_1409_ = v___x_1518_;
v___y_1410_ = v___x_1523_;
v___y_1411_ = v___x_1542_;
v___y_1412_ = v___y_1517_;
v___y_1413_ = v___x_1520_;
v___y_1414_ = v___x_1522_;
v___y_1415_ = v___y_1516_;
v___y_1416_ = v___x_1559_;
goto v___jp_1399_;
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___boxed(lean_object* v_x_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(v_x_1576_, v_a_1577_, v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1579_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = l_Lean_explicitBinders;
v___x_1587_ = ((lean_object*)(l_term_u2203___x2c___00__closed__3));
v___x_1588_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1589_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
lean_ctor_set(v___x_1589_, 2, v___x_1586_);
return v___x_1589_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1590_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1591_ = lean_obj_once(&l_term_u2203___x2c___00__closed__4, &l_term_u2203___x2c___00__closed__4_once, _init_l_term_u2203___x2c___00__closed__4);
v___x_1592_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1593_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1592_);
lean_ctor_set(v___x_1593_, 1, v___x_1591_);
lean_ctor_set(v___x_1593_, 2, v___x_1590_);
return v___x_1593_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1594_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1595_ = lean_obj_once(&l_term_u2203___x2c___00__closed__5, &l_term_u2203___x2c___00__closed__5_once, _init_l_term_u2203___x2c___00__closed__5);
v___x_1596_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1597_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
lean_ctor_set(v___x_1597_, 2, v___x_1594_);
return v___x_1597_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = lean_obj_once(&l_term_u2203___x2c___00__closed__6, &l_term_u2203___x2c___00__closed__6_once, _init_l_term_u2203___x2c___00__closed__6);
v___x_1599_ = lean_unsigned_to_nat(1022u);
v___x_1600_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_1601_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
lean_ctor_set(v___x_1601_, 2, v___x_1598_);
return v___x_1601_;
}
}
static lean_object* _init_l_term_u2203___x2c__(void){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_obj_once(&l_term_u2203___x2c___00__closed__7, &l_term_u2203___x2c___00__closed__7_once, _init_l_term_u2203___x2c___00__closed__7);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(lean_object* v_x_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v_x_1606_);
v___x_1610_ = l_Lean_Syntax_isOfKind(v_x_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
lean_dec(v_x_1606_);
v___x_1611_ = lean_box(1);
v___x_1612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1611_);
lean_ctor_set(v___x_1612_, 1, v_a_1608_);
return v___x_1612_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1613_ = lean_unsigned_to_nat(1u);
v___x_1614_ = l_Lean_Syntax_getArg(v_x_1606_, v___x_1613_);
v___x_1615_ = lean_unsigned_to_nat(3u);
v___x_1616_ = l_Lean_Syntax_getArg(v_x_1606_, v___x_1615_);
lean_dec(v_x_1606_);
v___x_1617_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1618_ = l_Lean_expandExplicitBinders(v___x_1617_, v___x_1614_, v___x_1616_, v_a_1607_, v_a_1608_);
lean_dec(v___x_1614_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___boxed(lean_object* v_x_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(v_x_1619_, v_a_1620_, v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1622_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1629_ = l_Lean_explicitBinders;
v___x_1630_ = ((lean_object*)(l_termExists___x2c___00__closed__3));
v___x_1631_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1632_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v___x_1629_);
return v___x_1632_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1633_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1634_ = lean_obj_once(&l_termExists___x2c___00__closed__4, &l_termExists___x2c___00__closed__4_once, _init_l_termExists___x2c___00__closed__4);
v___x_1635_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1636_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
lean_ctor_set(v___x_1636_, 1, v___x_1634_);
lean_ctor_set(v___x_1636_, 2, v___x_1633_);
return v___x_1636_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1637_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1638_ = lean_obj_once(&l_termExists___x2c___00__closed__5, &l_termExists___x2c___00__closed__5_once, _init_l_termExists___x2c___00__closed__5);
v___x_1639_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1640_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
lean_ctor_set(v___x_1640_, 2, v___x_1637_);
return v___x_1640_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = lean_obj_once(&l_termExists___x2c___00__closed__6, &l_termExists___x2c___00__closed__6_once, _init_l_termExists___x2c___00__closed__6);
v___x_1642_ = lean_unsigned_to_nat(1022u);
v___x_1643_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
v___x_1644_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
lean_ctor_set(v___x_1644_, 1, v___x_1642_);
lean_ctor_set(v___x_1644_, 2, v___x_1641_);
return v___x_1644_;
}
}
static lean_object* _init_l_termExists___x2c__(void){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_obj_once(&l_termExists___x2c___00__closed__7, &l_termExists___x2c___00__closed__7_once, _init_l_termExists___x2c___00__closed__7);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(lean_object* v_x_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1649_; uint8_t v___x_1650_; 
v___x_1649_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
lean_inc(v_x_1646_);
v___x_1650_ = l_Lean_Syntax_isOfKind(v_x_1646_, v___x_1649_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec(v_x_1646_);
v___x_1651_ = lean_box(1);
v___x_1652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1651_);
lean_ctor_set(v___x_1652_, 1, v_a_1648_);
return v___x_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1653_);
v___x_1655_ = lean_unsigned_to_nat(3u);
v___x_1656_ = l_Lean_Syntax_getArg(v_x_1646_, v___x_1655_);
lean_dec(v_x_1646_);
v___x_1657_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1658_ = l_Lean_expandExplicitBinders(v___x_1657_, v___x_1654_, v___x_1656_, v_a_1647_, v_a_1648_);
lean_dec(v___x_1654_);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1___boxed(lean_object* v_x_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(v_x_1659_, v_a_1660_, v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1662_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1669_ = l_Lean_explicitBinders;
v___x_1670_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__3));
v___x_1671_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1672_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
lean_ctor_set(v___x_1672_, 2, v___x_1669_);
return v___x_1672_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1673_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1674_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__4, &l_term_u03a3___x2c___00__closed__4_once, _init_l_term_u03a3___x2c___00__closed__4);
v___x_1675_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1676_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v___x_1674_);
lean_ctor_set(v___x_1676_, 2, v___x_1673_);
return v___x_1676_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1677_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1678_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__5, &l_term_u03a3___x2c___00__closed__5_once, _init_l_term_u03a3___x2c___00__closed__5);
v___x_1679_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1680_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
lean_ctor_set(v___x_1680_, 2, v___x_1677_);
return v___x_1680_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__6, &l_term_u03a3___x2c___00__closed__6_once, _init_l_term_u03a3___x2c___00__closed__6);
v___x_1682_ = lean_unsigned_to_nat(1022u);
v___x_1683_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
v___x_1684_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
lean_ctor_set(v___x_1684_, 1, v___x_1682_);
lean_ctor_set(v___x_1684_, 2, v___x_1681_);
return v___x_1684_;
}
}
static lean_object* _init_l_term_u03a3___x2c__(void){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__7, &l_term_u03a3___x2c___00__closed__7_once, _init_l_term_u03a3___x2c___00__closed__7);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(lean_object* v_x_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
lean_inc(v_x_1689_);
v___x_1693_ = l_Lean_Syntax_isOfKind(v_x_1689_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec(v_x_1689_);
v___x_1694_ = lean_box(1);
v___x_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v_a_1691_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = l_Lean_Syntax_getArg(v_x_1689_, v___x_1696_);
v___x_1698_ = lean_unsigned_to_nat(3u);
v___x_1699_ = l_Lean_Syntax_getArg(v_x_1689_, v___x_1698_);
lean_dec(v_x_1689_);
v___x_1700_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1701_ = l_Lean_expandExplicitBinders(v___x_1700_, v___x_1697_, v___x_1699_, v_a_1690_, v_a_1691_);
lean_dec(v___x_1697_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___boxed(lean_object* v_x_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(v_x_1702_, v_a_1703_, v_a_1704_);
lean_dec_ref(v_a_1703_);
return v_res_1705_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = l_Lean_explicitBinders;
v___x_1713_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__3));
v___x_1714_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1715_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___x_1713_);
lean_ctor_set(v___x_1715_, 2, v___x_1712_);
return v___x_1715_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1716_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1717_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__4, &l_term_u03a3_x27___x2c___00__closed__4_once, _init_l_term_u03a3_x27___x2c___00__closed__4);
v___x_1718_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1719_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
lean_ctor_set(v___x_1719_, 1, v___x_1717_);
lean_ctor_set(v___x_1719_, 2, v___x_1716_);
return v___x_1719_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1720_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1721_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__5, &l_term_u03a3_x27___x2c___00__closed__5_once, _init_l_term_u03a3_x27___x2c___00__closed__5);
v___x_1722_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1723_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
lean_ctor_set(v___x_1723_, 2, v___x_1720_);
return v___x_1723_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1724_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__6, &l_term_u03a3_x27___x2c___00__closed__6_once, _init_l_term_u03a3_x27___x2c___00__closed__6);
v___x_1725_ = lean_unsigned_to_nat(1022u);
v___x_1726_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
v___x_1727_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v___x_1725_);
lean_ctor_set(v___x_1727_, 2, v___x_1724_);
return v___x_1727_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c__(void){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__7, &l_term_u03a3_x27___x2c___00__closed__7_once, _init_l_term_u03a3_x27___x2c___00__closed__7);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(lean_object* v_x_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1735_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
lean_inc(v_x_1732_);
v___x_1736_ = l_Lean_Syntax_isOfKind(v_x_1732_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_x_1732_);
v___x_1737_ = lean_box(1);
v___x_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v_a_1734_);
return v___x_1738_;
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = l_Lean_Syntax_getArg(v_x_1732_, v___x_1739_);
v___x_1741_ = lean_unsigned_to_nat(3u);
v___x_1742_ = l_Lean_Syntax_getArg(v_x_1732_, v___x_1741_);
lean_dec(v_x_1732_);
v___x_1743_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1744_ = l_Lean_expandExplicitBinders(v___x_1743_, v___x_1740_, v___x_1742_, v_a_1733_, v_a_1734_);
lean_dec(v___x_1740_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___boxed(lean_object* v_x_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(v_x_1745_, v_a_1746_, v_a_1747_);
lean_dec_ref(v_a_1746_);
return v_res_1748_;
}
}
static lean_object* _init_l_term___xd7____1___closed__4(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = ((lean_object*)(l_term___xd7____1___closed__3));
v___x_1756_ = l_Lean_bracketedExplicitBinders;
v___x_1757_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1758_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
lean_ctor_set(v___x_1758_, 2, v___x_1755_);
return v___x_1758_;
}
}
static lean_object* _init_l_term___xd7____1___closed__6(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1762_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1763_ = lean_obj_once(&l_term___xd7____1___closed__4, &l_term___xd7____1___closed__4_once, _init_l_term___xd7____1___closed__4);
v___x_1764_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1765_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v___x_1763_);
lean_ctor_set(v___x_1765_, 2, v___x_1762_);
return v___x_1765_;
}
}
static lean_object* _init_l_term___xd7____1___closed__7(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1766_ = lean_obj_once(&l_term___xd7____1___closed__6, &l_term___xd7____1___closed__6_once, _init_l_term___xd7____1___closed__6);
v___x_1767_ = lean_unsigned_to_nat(35u);
v___x_1768_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_1769_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1767_);
lean_ctor_set(v___x_1769_, 2, v___x_1766_);
return v___x_1769_;
}
}
static lean_object* _init_l_term___xd7____1(void){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = lean_obj_once(&l_term___xd7____1___closed__7, &l_term___xd7____1___closed__7_once, _init_l_term___xd7____1___closed__7);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(lean_object* v_x_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___x_1774_; uint8_t v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_term___xd7____1___closed__1));
lean_inc(v_x_1771_);
v___x_1775_ = l_Lean_Syntax_isOfKind(v_x_1771_, v___x_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec(v_x_1771_);
v___x_1776_ = lean_box(1);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v_a_1773_);
return v___x_1777_;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1778_);
v___x_1780_ = lean_unsigned_to_nat(2u);
v___x_1781_ = l_Lean_Syntax_getArg(v_x_1771_, v___x_1780_);
lean_dec(v_x_1771_);
v___x_1782_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1783_ = l_Lean_expandBracketedBinders(v___x_1782_, v___x_1779_, v___x_1781_, v_a_1772_, v_a_1773_);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1___boxed(lean_object* v_x_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(v_x_1784_, v_a_1785_, v_a_1786_);
lean_dec_ref(v_a_1785_);
return v_res_1787_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__4(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1794_ = ((lean_object*)(l_term___xd7_x27____1___closed__3));
v___x_1795_ = l_Lean_bracketedExplicitBinders;
v___x_1796_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1797_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v___x_1795_);
lean_ctor_set(v___x_1797_, 2, v___x_1794_);
return v___x_1797_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__5(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1799_ = lean_obj_once(&l_term___xd7_x27____1___closed__4, &l_term___xd7_x27____1___closed__4_once, _init_l_term___xd7_x27____1___closed__4);
v___x_1800_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1801_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
lean_ctor_set(v___x_1801_, 1, v___x_1799_);
lean_ctor_set(v___x_1801_, 2, v___x_1798_);
return v___x_1801_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__6(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = lean_obj_once(&l_term___xd7_x27____1___closed__5, &l_term___xd7_x27____1___closed__5_once, _init_l_term___xd7_x27____1___closed__5);
v___x_1803_ = lean_unsigned_to_nat(35u);
v___x_1804_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_1805_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1803_);
lean_ctor_set(v___x_1805_, 2, v___x_1802_);
return v___x_1805_;
}
}
static lean_object* _init_l_term___xd7_x27____1(void){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_obj_once(&l_term___xd7_x27____1___closed__6, &l_term___xd7_x27____1___closed__6_once, _init_l_term___xd7_x27____1___closed__6);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(lean_object* v_x_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
lean_inc(v_x_1807_);
v___x_1811_ = l_Lean_Syntax_isOfKind(v_x_1807_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec(v_x_1807_);
v___x_1812_ = lean_box(1);
v___x_1813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v_a_1809_);
return v___x_1813_;
}
else
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = l_Lean_Syntax_getArg(v_x_1807_, v___x_1814_);
v___x_1816_ = lean_unsigned_to_nat(2u);
v___x_1817_ = l_Lean_Syntax_getArg(v_x_1807_, v___x_1816_);
lean_dec(v_x_1807_);
v___x_1818_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1819_ = l_Lean_expandBracketedBinders(v___x_1818_, v___x_1815_, v___x_1817_, v_a_1808_, v_a_1809_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1___boxed(lean_object* v_x_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(v_x_1820_, v_a_1821_, v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(lean_object* v_x_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1986_ = ((lean_object*)(l_Lean_convCalc___00__closed__1));
lean_inc(v_x_1983_);
v___x_1987_ = l_Lean_Syntax_isOfKind(v_x_1983_, v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec(v_x_1983_);
v___x_1988_ = lean_box(1);
v___x_1989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v_a_1985_);
return v___x_1989_;
}
else
{
lean_object* v_ref_1990_; lean_object* v___x_1991_; lean_object* v_tk_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_ref_1990_ = lean_ctor_get(v_a_1984_, 5);
v___x_1991_ = lean_unsigned_to_nat(0u);
v_tk_1992_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_1991_);
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = l_Lean_Syntax_getArg(v_x_1983_, v___x_1993_);
lean_dec(v_x_1983_);
v___x_1995_ = 0;
v___x_1996_ = l_Lean_SourceInfo_fromRef(v_ref_1990_, v___x_1995_);
v___x_1997_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3));
v___x_1998_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4));
lean_inc_n(v___x_1996_, 6);
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1996_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_2001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1996_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_2003_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_2004_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2005_ = ((lean_object*)(l_Lean_calcTactic___closed__1));
v___x_2006_ = l_Lean_SourceInfo_fromRef(v_tk_1992_, v___x_1987_);
lean_dec(v_tk_1992_);
v___x_2007_ = ((lean_object*)(l_Lean_calc___closed__0));
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l_Lean_Syntax_node2(v___x_1996_, v___x_2005_, v___x_2008_, v___x_1994_);
v___x_2010_ = l_Lean_Syntax_node1(v___x_1996_, v___x_2004_, v___x_2009_);
v___x_2011_ = l_Lean_Syntax_node1(v___x_1996_, v___x_2003_, v___x_2010_);
v___x_2012_ = l_Lean_Syntax_node1(v___x_1996_, v___x_2002_, v___x_2011_);
v___x_2013_ = l_Lean_Syntax_node3(v___x_1996_, v___x_1997_, v___x_1999_, v___x_2001_, v___x_2012_);
v___x_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_a_1985_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___boxed(lean_object* v_x_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(v_x_2015_, v_a_2016_, v_a_2017_);
lean_dec_ref(v_a_2016_);
return v_res_2018_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__9(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_unexpandUnit___redArg___closed__8));
v___x_2039_ = l_String_toRawSubstring_x27(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__10(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = lean_box(0);
v___x_2042_ = ((lean_object*)(l_unexpandUnit___redArg___closed__1));
v___x_2043_ = l_Lean_addMacroScope(v___x_2042_, v___x_2041_, v___x_2040_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg(lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2058_ = 0;
v___x_2059_ = l_Lean_SourceInfo_fromRef(v_a_2056_, v___x_2058_);
v___x_2060_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
v___x_2061_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_2062_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2059_, 6);
v___x_2063_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2059_);
lean_ctor_set(v___x_2063_, 1, v___x_2062_);
v___x_2064_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2065_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2066_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2067_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2068_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2059_);
lean_ctor_set(v___x_2068_, 1, v___x_2065_);
lean_ctor_set(v___x_2068_, 2, v___x_2066_);
lean_ctor_set(v___x_2068_, 3, v___x_2067_);
v___x_2069_ = l_Lean_Syntax_node1(v___x_2059_, v___x_2064_, v___x_2068_);
v___x_2070_ = l_Lean_Syntax_node2(v___x_2059_, v___x_2061_, v___x_2063_, v___x_2069_);
v___x_2071_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2072_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2073_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2059_);
lean_ctor_set(v___x_2073_, 1, v___x_2071_);
lean_ctor_set(v___x_2073_, 2, v___x_2072_);
v___x_2074_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2075_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2059_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_Syntax_node3(v___x_2059_, v___x_2060_, v___x_2070_, v___x_2073_, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2076_);
lean_ctor_set(v___x_2077_, 1, v_a_2057_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg___boxed(lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_unexpandUnit___redArg(v_a_2078_, v_a_2079_);
lean_dec(v_a_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit(lean_object* v_x_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_unexpandUnit___redArg(v_a_2082_, v_a_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___boxed(lean_object* v_x_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_unexpandUnit(v_x_2085_, v_a_2086_, v_a_2087_);
lean_dec(v_a_2086_);
lean_dec(v_x_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg(lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
uint8_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2095_ = 0;
v___x_2096_ = l_Lean_SourceInfo_fromRef(v_a_2093_, v___x_2095_);
v___x_2097_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
v___x_2098_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2096_, 3);
v___x_2099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2096_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2101_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2096_);
lean_ctor_set(v___x_2102_, 1, v___x_2100_);
lean_ctor_set(v___x_2102_, 2, v___x_2101_);
v___x_2103_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2096_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_Lean_Syntax_node3(v___x_2096_, v___x_2097_, v___x_2099_, v___x_2102_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2105_);
lean_ctor_set(v___x_2106_, 1, v_a_2094_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg___boxed(lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_unexpandListNil___redArg(v_a_2107_, v_a_2108_);
lean_dec(v_a_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil(lean_object* v_x_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_unexpandListNil___redArg(v_a_2111_, v_a_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___boxed(lean_object* v_x_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_unexpandListNil(v_x_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2115_);
lean_dec(v_x_2114_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_unexpandListCons(lean_object* v_x_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2127_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2124_);
v___x_2128_ = l_Lean_Syntax_isOfKind(v_x_2124_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec(v_x_2124_);
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v_a_2126_);
return v___x_2130_;
}
else
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = l_Lean_Syntax_getArg(v_x_2124_, v___x_2131_);
lean_dec(v_x_2124_);
v___x_2133_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2132_);
v___x_2134_ = l_Lean_Syntax_matchesNull(v___x_2132_, v___x_2133_);
if (v___x_2134_ == 0)
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v___x_2132_);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
lean_ctor_set(v___x_2136_, 1, v_a_2126_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; uint8_t v___x_2141_; 
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = l_Lean_Syntax_getArg(v___x_2132_, v___x_2137_);
v___x_2139_ = l_Lean_Syntax_getArg(v___x_2132_, v___x_2131_);
lean_dec(v___x_2132_);
v___x_2140_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2139_);
v___x_2141_ = l_Lean_Syntax_isOfKind(v___x_2139_, v___x_2140_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2142_ = ((lean_object*)(l_unexpandListCons___closed__1));
lean_inc(v___x_2139_);
v___x_2143_ = l_Lean_Syntax_isOfKind(v___x_2139_, v___x_2142_);
if (v___x_2143_ == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec(v___x_2139_);
lean_dec(v___x_2138_);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_a_2126_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2146_ = l_Lean_SourceInfo_fromRef(v_a_2125_, v___x_2141_);
v___x_2147_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2146_, 4);
v___x_2148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2150_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2146_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_node3(v___x_2146_, v___x_2149_, v___x_2138_, v___x_2151_, v___x_2139_);
v___x_2153_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2146_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = l_Lean_Syntax_node3(v___x_2146_, v___x_2140_, v___x_2148_, v___x_2152_, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2155_);
lean_ctor_set(v___x_2156_, 1, v_a_2126_);
return v___x_2156_;
}
}
else
{
lean_object* v___x_2157_; uint8_t v___x_2158_; 
v___x_2157_ = l_Lean_Syntax_getArg(v___x_2139_, v___x_2131_);
lean_dec(v___x_2139_);
lean_inc(v___x_2157_);
v___x_2158_ = l_Lean_Syntax_matchesNull(v___x_2157_, v___x_2137_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2159_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2160_ = l_Lean_Syntax_getArgs(v___x_2157_);
lean_dec(v___x_2157_);
v___x_2161_ = l_Lean_SourceInfo_fromRef(v_a_2125_, v___x_2158_);
v___x_2162_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2161_, 4);
v___x_2163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2161_);
lean_ctor_set(v___x_2165_, 1, v___x_2159_);
v___x_2166_ = l_Array_mkArray2___redArg(v___x_2138_, v___x_2165_);
v___x_2167_ = l_Array_append___redArg(v___x_2166_, v___x_2160_);
lean_dec_ref(v___x_2160_);
v___x_2168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2161_);
lean_ctor_set(v___x_2168_, 1, v___x_2164_);
lean_ctor_set(v___x_2168_, 2, v___x_2167_);
v___x_2169_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2170_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2161_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = l_Lean_Syntax_node3(v___x_2161_, v___x_2140_, v___x_2163_, v___x_2168_, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_a_2126_);
return v___x_2172_;
}
else
{
uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v___x_2157_);
v___x_2173_ = 0;
v___x_2174_ = l_Lean_SourceInfo_fromRef(v_a_2125_, v___x_2173_);
v___x_2175_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2174_, 3);
v___x_2176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2178_ = l_Lean_Syntax_node1(v___x_2174_, v___x_2177_, v___x_2138_);
v___x_2179_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2174_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = l_Lean_Syntax_node3(v___x_2174_, v___x_2140_, v___x_2176_, v___x_2178_, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_a_2126_);
return v___x_2182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListCons___boxed(lean_object* v_x_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_unexpandListCons(v_x_2183_, v_a_2184_, v_a_2185_);
lean_dec(v_a_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray(lean_object* v_x_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2194_; uint8_t v___x_2195_; 
v___x_2194_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2191_);
v___x_2195_ = l_Lean_Syntax_isOfKind(v_x_2191_, v___x_2194_);
if (v___x_2195_ == 0)
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_x_2191_);
v___x_2196_ = lean_box(0);
v___x_2197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v_a_2193_);
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = l_Lean_Syntax_getArg(v_x_2191_, v___x_2198_);
lean_dec(v_x_2191_);
lean_inc(v___x_2199_);
v___x_2200_ = l_Lean_Syntax_matchesNull(v___x_2199_, v___x_2198_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v___x_2199_);
v___x_2201_ = lean_box(0);
v___x_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v_a_2193_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; uint8_t v___x_2206_; 
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = l_Lean_Syntax_getArg(v___x_2199_, v___x_2203_);
lean_dec(v___x_2199_);
v___x_2205_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2204_);
v___x_2206_ = l_Lean_Syntax_isOfKind(v___x_2204_, v___x_2205_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v___x_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v_a_2193_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; uint8_t v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2209_ = l_Lean_Syntax_getArg(v___x_2204_, v___x_2198_);
lean_dec(v___x_2204_);
v___x_2210_ = l_Lean_Syntax_getArgs(v___x_2209_);
lean_dec(v___x_2209_);
v___x_2211_ = 0;
v___x_2212_ = l_Lean_SourceInfo_fromRef(v_a_2192_, v___x_2211_);
v___x_2213_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_2214_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_2212_, 3);
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2212_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2217_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2218_ = l_Array_append___redArg(v___x_2217_, v___x_2210_);
lean_dec_ref(v___x_2210_);
v___x_2219_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2212_);
lean_ctor_set(v___x_2219_, 1, v___x_2216_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
v___x_2220_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2221_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2212_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___x_2222_ = l_Lean_Syntax_node3(v___x_2212_, v___x_2213_, v___x_2215_, v___x_2219_, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v_a_2193_);
return v___x_2223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray___boxed(lean_object* v_x_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_unexpandListToArray(v_x_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk(lean_object* v_x_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2231_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2228_);
v___x_2232_ = l_Lean_Syntax_isOfKind(v_x_2228_, v___x_2231_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
lean_dec(v_x_2228_);
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v_a_2230_);
return v___x_2234_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = l_Lean_Syntax_getArg(v_x_2228_, v___x_2235_);
lean_dec(v_x_2228_);
v___x_2237_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2236_);
v___x_2238_ = l_Lean_Syntax_matchesNull(v___x_2236_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v___x_2236_);
v___x_2239_ = lean_box(0);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2239_);
lean_ctor_set(v___x_2240_, 1, v_a_2230_);
return v___x_2240_;
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = l_Lean_Syntax_getArg(v___x_2236_, v___x_2241_);
v___x_2243_ = l_Lean_Syntax_getArg(v___x_2236_, v___x_2235_);
lean_dec(v___x_2236_);
v___x_2244_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
lean_inc(v___x_2243_);
v___x_2245_ = l_Lean_Syntax_isOfKind(v___x_2243_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2246_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2245_);
v___x_2247_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_2248_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2246_, 8);
v___x_2249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2246_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2251_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2252_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2253_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2254_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2246_);
lean_ctor_set(v___x_2254_, 1, v___x_2251_);
lean_ctor_set(v___x_2254_, 2, v___x_2252_);
lean_ctor_set(v___x_2254_, 3, v___x_2253_);
v___x_2255_ = l_Lean_Syntax_node1(v___x_2246_, v___x_2250_, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node2(v___x_2246_, v___x_2247_, v___x_2249_, v___x_2255_);
v___x_2257_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2258_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2259_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2246_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v___x_2260_ = l_Lean_Syntax_node1(v___x_2246_, v___x_2257_, v___x_2243_);
v___x_2261_ = l_Lean_Syntax_node3(v___x_2246_, v___x_2257_, v___x_2242_, v___x_2259_, v___x_2260_);
v___x_2262_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2246_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = l_Lean_Syntax_node3(v___x_2246_, v___x_2244_, v___x_2256_, v___x_2261_, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_a_2230_);
return v___x_2265_;
}
else
{
lean_object* v___x_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2266_ = l_Lean_Syntax_getArg(v___x_2243_, v___x_2241_);
v___x_2267_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2266_);
v___x_2268_ = l_Lean_Syntax_isOfKind(v___x_2266_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v___x_2266_);
v___x_2269_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2268_);
v___x_2270_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2269_, 8);
v___x_2271_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2269_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2273_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2274_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2275_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2269_);
lean_ctor_set(v___x_2276_, 1, v___x_2273_);
lean_ctor_set(v___x_2276_, 2, v___x_2274_);
lean_ctor_set(v___x_2276_, 3, v___x_2275_);
v___x_2277_ = l_Lean_Syntax_node1(v___x_2269_, v___x_2272_, v___x_2276_);
v___x_2278_ = l_Lean_Syntax_node2(v___x_2269_, v___x_2267_, v___x_2271_, v___x_2277_);
v___x_2279_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2280_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2269_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = l_Lean_Syntax_node1(v___x_2269_, v___x_2279_, v___x_2243_);
v___x_2283_ = l_Lean_Syntax_node3(v___x_2269_, v___x_2279_, v___x_2242_, v___x_2281_, v___x_2282_);
v___x_2284_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2269_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_node3(v___x_2269_, v___x_2244_, v___x_2278_, v___x_2283_, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_a_2230_);
return v___x_2287_;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2288_ = l_Lean_Syntax_getArg(v___x_2266_, v___x_2235_);
lean_dec(v___x_2266_);
v___x_2289_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2288_);
v___x_2290_ = l_Lean_Syntax_isOfKind(v___x_2288_, v___x_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_dec(v___x_2288_);
v___x_2291_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2290_);
v___x_2292_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2291_, 8);
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2295_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2296_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2297_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2291_);
lean_ctor_set(v___x_2297_, 1, v___x_2294_);
lean_ctor_set(v___x_2297_, 2, v___x_2295_);
lean_ctor_set(v___x_2297_, 3, v___x_2296_);
v___x_2298_ = l_Lean_Syntax_node1(v___x_2291_, v___x_2289_, v___x_2297_);
v___x_2299_ = l_Lean_Syntax_node2(v___x_2291_, v___x_2267_, v___x_2293_, v___x_2298_);
v___x_2300_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2301_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2302_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2291_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = l_Lean_Syntax_node1(v___x_2291_, v___x_2300_, v___x_2243_);
v___x_2304_ = l_Lean_Syntax_node3(v___x_2291_, v___x_2300_, v___x_2242_, v___x_2302_, v___x_2303_);
v___x_2305_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2291_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = l_Lean_Syntax_node3(v___x_2291_, v___x_2244_, v___x_2299_, v___x_2304_, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v_a_2230_);
return v___x_2308_;
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2309_ = l_Lean_Syntax_getArg(v___x_2288_, v___x_2241_);
lean_dec(v___x_2288_);
v___x_2310_ = lean_box(0);
v___x_2311_ = l_Lean_Syntax_matchesIdent(v___x_2309_, v___x_2310_);
lean_dec(v___x_2309_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2312_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2311_);
v___x_2313_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2312_, 8);
v___x_2314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2316_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2317_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2318_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2312_);
lean_ctor_set(v___x_2318_, 1, v___x_2315_);
lean_ctor_set(v___x_2318_, 2, v___x_2316_);
lean_ctor_set(v___x_2318_, 3, v___x_2317_);
v___x_2319_ = l_Lean_Syntax_node1(v___x_2312_, v___x_2289_, v___x_2318_);
v___x_2320_ = l_Lean_Syntax_node2(v___x_2312_, v___x_2267_, v___x_2314_, v___x_2319_);
v___x_2321_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2322_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2312_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_Syntax_node1(v___x_2312_, v___x_2321_, v___x_2243_);
v___x_2325_ = l_Lean_Syntax_node3(v___x_2312_, v___x_2321_, v___x_2242_, v___x_2323_, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2312_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = l_Lean_Syntax_node3(v___x_2312_, v___x_2244_, v___x_2320_, v___x_2325_, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v_a_2230_);
return v___x_2329_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2330_ = l_Lean_Syntax_getArg(v___x_2243_, v___x_2235_);
v___x_2331_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2330_);
v___x_2332_ = l_Lean_Syntax_matchesNull(v___x_2330_, v___x_2331_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v___x_2330_);
v___x_2333_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2332_);
v___x_2334_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2333_, 8);
v___x_2335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
v___x_2336_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2337_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2338_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2339_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2333_);
lean_ctor_set(v___x_2339_, 1, v___x_2336_);
lean_ctor_set(v___x_2339_, 2, v___x_2337_);
lean_ctor_set(v___x_2339_, 3, v___x_2338_);
v___x_2340_ = l_Lean_Syntax_node1(v___x_2333_, v___x_2289_, v___x_2339_);
v___x_2341_ = l_Lean_Syntax_node2(v___x_2333_, v___x_2267_, v___x_2335_, v___x_2340_);
v___x_2342_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2343_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2333_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = l_Lean_Syntax_node1(v___x_2333_, v___x_2342_, v___x_2243_);
v___x_2346_ = l_Lean_Syntax_node3(v___x_2333_, v___x_2342_, v___x_2242_, v___x_2344_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2333_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = l_Lean_Syntax_node3(v___x_2333_, v___x_2244_, v___x_2341_, v___x_2346_, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_a_2230_);
return v___x_2350_;
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v___x_2243_);
v___x_2351_ = l_Lean_Syntax_getArg(v___x_2330_, v___x_2241_);
v___x_2352_ = l_Lean_Syntax_getArg(v___x_2330_, v___x_2237_);
lean_dec(v___x_2330_);
v___x_2353_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2354_ = l_Lean_Syntax_getArgs(v___x_2352_);
lean_dec(v___x_2352_);
v___x_2355_ = 0;
v___x_2356_ = l_Lean_SourceInfo_fromRef(v_a_2229_, v___x_2355_);
v___x_2357_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2356_, 8);
v___x_2358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2360_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2361_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2362_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2359_);
lean_ctor_set(v___x_2362_, 2, v___x_2360_);
lean_ctor_set(v___x_2362_, 3, v___x_2361_);
v___x_2363_ = l_Lean_Syntax_node1(v___x_2356_, v___x_2289_, v___x_2362_);
v___x_2364_ = l_Lean_Syntax_node2(v___x_2356_, v___x_2267_, v___x_2358_, v___x_2363_);
v___x_2365_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2356_);
lean_ctor_set(v___x_2366_, 1, v___x_2353_);
lean_inc_ref(v___x_2366_);
v___x_2367_ = l_Array_mkArray2___redArg(v___x_2351_, v___x_2366_);
v___x_2368_ = l_Array_append___redArg(v___x_2367_, v___x_2354_);
lean_dec_ref(v___x_2354_);
v___x_2369_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2356_);
lean_ctor_set(v___x_2369_, 1, v___x_2365_);
lean_ctor_set(v___x_2369_, 2, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node3(v___x_2356_, v___x_2365_, v___x_2242_, v___x_2366_, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2356_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_Syntax_node3(v___x_2356_, v___x_2244_, v___x_2364_, v___x_2370_, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
lean_ctor_set(v___x_2374_, 1, v_a_2230_);
return v___x_2374_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk___boxed(lean_object* v_x_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_unexpandProdMk(v_x_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2376_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_unexpandIte(lean_object* v_x_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2388_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2385_);
v___x_2389_ = l_Lean_Syntax_isOfKind(v_x_2385_, v___x_2388_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_x_2385_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_a_2387_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = l_Lean_Syntax_getArg(v_x_2385_, v___x_2392_);
lean_dec(v_x_2385_);
v___x_2394_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2393_);
v___x_2395_ = l_Lean_Syntax_matchesNull(v___x_2393_, v___x_2394_);
if (v___x_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v___x_2397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
lean_ctor_set(v___x_2397_, 1, v_a_2387_);
return v___x_2397_;
}
else
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2398_ = lean_unsigned_to_nat(0u);
v___x_2399_ = l_Lean_Syntax_getArg(v___x_2393_, v___x_2398_);
v___x_2400_ = l_Lean_Syntax_getArg(v___x_2393_, v___x_2392_);
v___x_2401_ = lean_unsigned_to_nat(2u);
v___x_2402_ = l_Lean_Syntax_getArg(v___x_2393_, v___x_2401_);
lean_dec(v___x_2393_);
v___x_2403_ = 0;
v___x_2404_ = l_Lean_SourceInfo_fromRef(v_a_2386_, v___x_2403_);
v___x_2405_ = ((lean_object*)(l_unexpandIte___closed__1));
v___x_2406_ = ((lean_object*)(l_unexpandIte___closed__2));
lean_inc_n(v___x_2404_, 3);
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2404_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_unexpandIte___closed__3));
v___x_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2404_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_unexpandIte___closed__4));
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2404_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = l_Lean_Syntax_node6(v___x_2404_, v___x_2405_, v___x_2407_, v___x_2399_, v___x_2409_, v___x_2400_, v___x_2411_, v___x_2402_);
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v_a_2387_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandIte___boxed(lean_object* v_x_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_){
_start:
{
lean_object* v_res_2417_; 
v_res_2417_ = l_unexpandIte(v_x_2414_, v_a_2415_, v_a_2416_);
lean_dec(v_a_2415_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec(lean_object* v_x_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2428_; uint8_t v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2425_);
v___x_2429_ = l_Lean_Syntax_isOfKind(v_x_2425_, v___x_2428_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_dec(v_x_2425_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v_a_2427_);
return v___x_2431_;
}
else
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v___x_2432_ = lean_unsigned_to_nat(1u);
v___x_2433_ = l_Lean_Syntax_getArg(v_x_2425_, v___x_2432_);
lean_dec(v_x_2425_);
v___x_2434_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2433_);
v___x_2435_ = l_Lean_Syntax_matchesNull(v___x_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v_a_2427_);
return v___x_2437_;
}
else
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2438_ = lean_unsigned_to_nat(0u);
v___x_2439_ = l_Lean_Syntax_getArg(v___x_2433_, v___x_2438_);
v___x_2440_ = l_Lean_Syntax_getArg(v___x_2433_, v___x_2432_);
lean_dec(v___x_2433_);
v___x_2441_ = 0;
v___x_2442_ = l_Lean_SourceInfo_fromRef(v_a_2426_, v___x_2441_);
v___x_2443_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2444_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc(v___x_2442_);
v___x_2445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2442_);
lean_ctor_set(v___x_2445_, 1, v___x_2444_);
v___x_2446_ = l_Lean_Syntax_node3(v___x_2442_, v___x_2443_, v___x_2440_, v___x_2445_, v___x_2439_);
v___x_2447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v_a_2427_);
return v___x_2447_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec___boxed(lean_object* v_x_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_unexpandEqNDRec(v_x_2448_, v_a_2449_, v_a_2450_);
lean_dec(v_a_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec(lean_object* v_x_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2455_; uint8_t v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2452_);
v___x_2456_ = l_Lean_Syntax_isOfKind(v_x_2452_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v_x_2452_);
v___x_2457_ = lean_box(0);
v___x_2458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_a_2454_);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = l_Lean_Syntax_getArg(v_x_2452_, v___x_2459_);
lean_dec(v_x_2452_);
v___x_2461_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2460_);
v___x_2462_ = l_Lean_Syntax_matchesNull(v___x_2460_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v___x_2464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v_a_2454_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = l_Lean_Syntax_getArg(v___x_2460_, v___x_2465_);
v___x_2467_ = l_Lean_Syntax_getArg(v___x_2460_, v___x_2459_);
lean_dec(v___x_2460_);
v___x_2468_ = 0;
v___x_2469_ = l_Lean_SourceInfo_fromRef(v_a_2453_, v___x_2468_);
v___x_2470_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2471_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc(v___x_2469_);
v___x_2472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2469_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = l_Lean_Syntax_node3(v___x_2469_, v___x_2470_, v___x_2467_, v___x_2472_, v___x_2466_);
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v___x_2473_);
lean_ctor_set(v___x_2474_, 1, v_a_2454_);
return v___x_2474_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec___boxed(lean_object* v_x_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_unexpandEqRec(v_x_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_unexpandExists(lean_object* v_x_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2492_; uint8_t v___x_2493_; 
v___x_2492_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2489_);
v___x_2493_ = l_Lean_Syntax_isOfKind(v_x_2489_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v_x_2489_);
v___x_2494_ = lean_box(0);
v___x_2495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v_a_2491_);
return v___x_2495_;
}
else
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; 
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = l_Lean_Syntax_getArg(v_x_2489_, v___x_2496_);
lean_dec(v_x_2489_);
lean_inc(v___x_2497_);
v___x_2498_ = l_Lean_Syntax_matchesNull(v___x_2497_, v___x_2496_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
lean_dec(v___x_2497_);
v___x_2499_ = lean_box(0);
v___x_2500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
lean_ctor_set(v___x_2500_, 1, v_a_2491_);
return v___x_2500_;
}
else
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; uint8_t v___x_2504_; 
v___x_2501_ = lean_unsigned_to_nat(0u);
v___x_2502_ = l_Lean_Syntax_getArg(v___x_2497_, v___x_2501_);
lean_dec(v___x_2497_);
v___x_2503_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2502_);
v___x_2504_ = l_Lean_Syntax_isOfKind(v___x_2502_, v___x_2503_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v___x_2506_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2505_);
lean_ctor_set(v___x_2506_, 1, v_a_2491_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; uint8_t v___x_2509_; 
v___x_2507_ = l_Lean_Syntax_getArg(v___x_2502_, v___x_2496_);
lean_dec(v___x_2502_);
v___x_2508_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2507_);
v___x_2509_ = l_Lean_Syntax_isOfKind(v___x_2507_, v___x_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v___x_2507_);
v___x_2510_ = lean_box(0);
v___x_2511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2511_, 0, v___x_2510_);
lean_ctor_set(v___x_2511_, 1, v_a_2491_);
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; uint8_t v___x_2513_; 
v___x_2512_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2501_);
lean_inc(v___x_2512_);
v___x_2513_ = l_Lean_Syntax_matchesNull(v___x_2512_, v___x_2496_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v___x_2512_);
lean_dec(v___x_2507_);
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2514_);
lean_ctor_set(v___x_2515_, 1, v_a_2491_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2516_ = l_Lean_Syntax_getArg(v___x_2512_, v___x_2501_);
lean_dec(v___x_2512_);
v___x_2517_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2516_);
v___x_2518_ = l_Lean_Syntax_isOfKind(v___x_2516_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2519_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2516_);
v___x_2520_ = l_Lean_Syntax_isOfKind(v___x_2516_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v_a_2491_);
return v___x_2522_;
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2523_ = l_Lean_Syntax_getArg(v___x_2516_, v___x_2501_);
v___x_2524_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2523_);
v___x_2525_ = l_Lean_Syntax_isOfKind(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v___x_2523_);
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2526_ = lean_box(0);
v___x_2527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v_a_2491_);
return v___x_2527_;
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2528_ = l_Lean_Syntax_getArg(v___x_2523_, v___x_2496_);
lean_dec(v___x_2523_);
v___x_2529_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2528_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v___x_2528_);
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_a_2491_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = l_Lean_Syntax_getArg(v___x_2528_, v___x_2501_);
lean_dec(v___x_2528_);
v___x_2534_ = lean_box(0);
v___x_2535_ = l_Lean_Syntax_matchesIdent(v___x_2533_, v___x_2534_);
lean_dec(v___x_2533_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v_a_2491_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = l_Lean_Syntax_getArg(v___x_2516_, v___x_2496_);
lean_inc(v___x_2538_);
v___x_2539_ = l_Lean_Syntax_isOfKind(v___x_2538_, v___x_2517_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
lean_dec(v___x_2538_);
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2540_ = lean_box(0);
v___x_2541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v_a_2491_);
return v___x_2541_;
}
else
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2542_ = lean_unsigned_to_nat(3u);
v___x_2543_ = l_Lean_Syntax_getArg(v___x_2516_, v___x_2542_);
lean_dec(v___x_2516_);
lean_inc(v___x_2543_);
v___x_2544_ = l_Lean_Syntax_matchesNull(v___x_2543_, v___x_2496_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec(v___x_2543_);
lean_dec(v___x_2538_);
lean_dec(v___x_2507_);
v___x_2545_ = lean_box(0);
v___x_2546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
lean_ctor_set(v___x_2546_, 1, v_a_2491_);
return v___x_2546_;
}
else
{
lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2547_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2496_);
v___x_2548_ = l_Lean_Syntax_matchesNull(v___x_2547_, v___x_2501_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec(v___x_2543_);
lean_dec(v___x_2538_);
lean_dec(v___x_2507_);
v___x_2549_ = lean_box(0);
v___x_2550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v_a_2491_);
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2551_ = l_Lean_Syntax_getArg(v___x_2543_, v___x_2501_);
lean_dec(v___x_2543_);
v___x_2552_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2542_);
lean_dec(v___x_2507_);
v___x_2553_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2518_);
v___x_2554_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_2555_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2553_, 10);
v___x_2556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2553_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2558_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2559_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2560_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_2561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2553_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2563_ = l_Lean_Syntax_node1(v___x_2553_, v___x_2562_, v___x_2538_);
v___x_2564_ = l_Lean_Syntax_node1(v___x_2553_, v___x_2558_, v___x_2563_);
v___x_2565_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2566_, 0, v___x_2553_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2553_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l_Lean_Syntax_node5(v___x_2553_, v___x_2559_, v___x_2561_, v___x_2564_, v___x_2566_, v___x_2551_, v___x_2568_);
v___x_2570_ = l_Lean_Syntax_node1(v___x_2553_, v___x_2558_, v___x_2569_);
v___x_2571_ = l_Lean_Syntax_node1(v___x_2553_, v___x_2557_, v___x_2570_);
v___x_2572_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2553_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = l_Lean_Syntax_node4(v___x_2553_, v___x_2554_, v___x_2556_, v___x_2571_, v___x_2573_, v___x_2552_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v_a_2491_);
return v___x_2575_;
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
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2496_);
v___x_2577_ = l_Lean_Syntax_matchesNull(v___x_2576_, v___x_2501_);
if (v___x_2577_ == 0)
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec(v___x_2516_);
lean_dec(v___x_2507_);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
lean_ctor_set(v___x_2579_, 1, v_a_2491_);
return v___x_2579_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2580_ = lean_unsigned_to_nat(3u);
v___x_2581_ = l_Lean_Syntax_getArg(v___x_2507_, v___x_2580_);
lean_dec(v___x_2507_);
v___x_2582_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v___x_2581_);
v___x_2583_ = l_Lean_Syntax_isOfKind(v___x_2581_, v___x_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2584_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2584_, 7);
v___x_2586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2588_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2589_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2590_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2591_ = l_Lean_Syntax_node1(v___x_2584_, v___x_2590_, v___x_2516_);
v___x_2592_ = l_Lean_Syntax_node1(v___x_2584_, v___x_2589_, v___x_2591_);
v___x_2593_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2584_);
lean_ctor_set(v___x_2594_, 1, v___x_2589_);
lean_ctor_set(v___x_2594_, 2, v___x_2593_);
v___x_2595_ = l_Lean_Syntax_node2(v___x_2584_, v___x_2588_, v___x_2592_, v___x_2594_);
v___x_2596_ = l_Lean_Syntax_node1(v___x_2584_, v___x_2587_, v___x_2595_);
v___x_2597_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2584_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = l_Lean_Syntax_node4(v___x_2584_, v___x_2582_, v___x_2586_, v___x_2596_, v___x_2598_, v___x_2581_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v_a_2491_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; uint8_t v___x_2603_; 
v___x_2601_ = l_Lean_Syntax_getArg(v___x_2581_, v___x_2496_);
v___x_2602_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
lean_inc(v___x_2601_);
v___x_2603_ = l_Lean_Syntax_isOfKind(v___x_2601_, v___x_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v___x_2601_);
v___x_2604_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2603_);
v___x_2605_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2604_, 7);
v___x_2606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
v___x_2607_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2608_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2609_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2610_ = l_Lean_Syntax_node1(v___x_2604_, v___x_2609_, v___x_2516_);
v___x_2611_ = l_Lean_Syntax_node1(v___x_2604_, v___x_2608_, v___x_2610_);
v___x_2612_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2604_);
lean_ctor_set(v___x_2613_, 1, v___x_2608_);
lean_ctor_set(v___x_2613_, 2, v___x_2612_);
v___x_2614_ = l_Lean_Syntax_node2(v___x_2604_, v___x_2607_, v___x_2611_, v___x_2613_);
v___x_2615_ = l_Lean_Syntax_node1(v___x_2604_, v___x_2602_, v___x_2614_);
v___x_2616_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2604_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = l_Lean_Syntax_node4(v___x_2604_, v___x_2582_, v___x_2606_, v___x_2615_, v___x_2617_, v___x_2581_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v_a_2491_);
return v___x_2619_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = l_Lean_Syntax_getArg(v___x_2601_, v___x_2501_);
lean_dec(v___x_2601_);
v___x_2621_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
lean_inc(v___x_2620_);
v___x_2622_ = l_Lean_Syntax_isOfKind(v___x_2620_, v___x_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
lean_dec(v___x_2620_);
v___x_2623_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2622_);
v___x_2624_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2623_, 7);
v___x_2625_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2627_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2628_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2627_, v___x_2516_);
v___x_2629_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2626_, v___x_2628_);
v___x_2630_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2623_);
lean_ctor_set(v___x_2631_, 1, v___x_2626_);
lean_ctor_set(v___x_2631_, 2, v___x_2630_);
v___x_2632_ = l_Lean_Syntax_node2(v___x_2623_, v___x_2621_, v___x_2629_, v___x_2631_);
v___x_2633_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2602_, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2623_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_Syntax_node4(v___x_2623_, v___x_2582_, v___x_2625_, v___x_2633_, v___x_2635_, v___x_2581_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
lean_ctor_set(v___x_2637_, 1, v_a_2491_);
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; uint8_t v___x_2639_; 
v___x_2638_ = l_Lean_Syntax_getArg(v___x_2620_, v___x_2496_);
v___x_2639_ = l_Lean_Syntax_matchesNull(v___x_2638_, v___x_2501_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v___x_2620_);
v___x_2640_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2639_);
v___x_2641_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2640_, 7);
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2644_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2645_ = l_Lean_Syntax_node1(v___x_2640_, v___x_2644_, v___x_2516_);
v___x_2646_ = l_Lean_Syntax_node1(v___x_2640_, v___x_2643_, v___x_2645_);
v___x_2647_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2648_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2640_);
lean_ctor_set(v___x_2648_, 1, v___x_2643_);
lean_ctor_set(v___x_2648_, 2, v___x_2647_);
v___x_2649_ = l_Lean_Syntax_node2(v___x_2640_, v___x_2621_, v___x_2646_, v___x_2648_);
v___x_2650_ = l_Lean_Syntax_node1(v___x_2640_, v___x_2602_, v___x_2649_);
v___x_2651_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2652_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2640_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = l_Lean_Syntax_node4(v___x_2640_, v___x_2582_, v___x_2642_, v___x_2650_, v___x_2652_, v___x_2581_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v_a_2491_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v_xs_2658_; uint8_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2655_ = l_Lean_Syntax_getArg(v___x_2620_, v___x_2501_);
lean_dec(v___x_2620_);
v___x_2656_ = l_Lean_Syntax_getArg(v___x_2581_, v___x_2580_);
lean_dec(v___x_2581_);
v___x_2657_ = ((lean_object*)(l_unexpandExists___closed__3));
v_xs_2658_ = l_Lean_Syntax_getArgs(v___x_2655_);
lean_dec(v___x_2655_);
v___x_2659_ = 0;
v___x_2660_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2659_);
v___x_2661_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2660_, 7);
v___x_2662_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2664_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2657_, v___x_2516_);
v___x_2665_ = l_Array_mkArray1___redArg(v___x_2664_);
v___x_2666_ = l_Array_append___redArg(v___x_2665_, v_xs_2658_);
lean_dec_ref(v_xs_2658_);
v___x_2667_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2660_);
lean_ctor_set(v___x_2667_, 1, v___x_2663_);
lean_ctor_set(v___x_2667_, 2, v___x_2666_);
v___x_2668_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2669_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2660_);
lean_ctor_set(v___x_2669_, 1, v___x_2663_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
v___x_2670_ = l_Lean_Syntax_node2(v___x_2660_, v___x_2621_, v___x_2667_, v___x_2669_);
v___x_2671_ = l_Lean_Syntax_node1(v___x_2660_, v___x_2602_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2673_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2660_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = l_Lean_Syntax_node4(v___x_2660_, v___x_2582_, v___x_2662_, v___x_2671_, v___x_2673_, v___x_2656_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v_a_2491_);
return v___x_2675_;
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
LEAN_EXPORT lean_object* l_unexpandExists___boxed(lean_object* v_x_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_unexpandExists(v_x_2676_, v_a_2677_, v_a_2678_);
lean_dec(v_a_2677_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_unexpandSigma(lean_object* v_x_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2681_);
v___x_2685_ = l_Lean_Syntax_isOfKind(v_x_2681_, v___x_2684_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec(v_x_2681_);
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v_a_2683_);
return v___x_2687_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = l_Lean_Syntax_getArg(v_x_2681_, v___x_2688_);
lean_dec(v_x_2681_);
lean_inc(v___x_2689_);
v___x_2690_ = l_Lean_Syntax_matchesNull(v___x_2689_, v___x_2688_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec(v___x_2689_);
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v_a_2683_);
return v___x_2692_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; 
v___x_2693_ = lean_unsigned_to_nat(0u);
v___x_2694_ = l_Lean_Syntax_getArg(v___x_2689_, v___x_2693_);
lean_dec(v___x_2689_);
v___x_2695_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2694_);
v___x_2696_ = l_Lean_Syntax_isOfKind(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v___x_2698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_a_2683_);
return v___x_2698_;
}
else
{
lean_object* v___x_2699_; lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2699_ = l_Lean_Syntax_getArg(v___x_2694_, v___x_2688_);
lean_dec(v___x_2694_);
v___x_2700_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2699_);
v___x_2701_ = l_Lean_Syntax_isOfKind(v___x_2699_, v___x_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec(v___x_2699_);
v___x_2702_ = lean_box(0);
v___x_2703_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
lean_ctor_set(v___x_2703_, 1, v_a_2683_);
return v___x_2703_;
}
else
{
lean_object* v___x_2704_; uint8_t v___x_2705_; 
v___x_2704_ = l_Lean_Syntax_getArg(v___x_2699_, v___x_2693_);
lean_inc(v___x_2704_);
v___x_2705_ = l_Lean_Syntax_matchesNull(v___x_2704_, v___x_2688_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
lean_dec(v___x_2704_);
lean_dec(v___x_2699_);
v___x_2706_ = lean_box(0);
v___x_2707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v_a_2683_);
return v___x_2707_;
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2708_ = l_Lean_Syntax_getArg(v___x_2704_, v___x_2693_);
lean_dec(v___x_2704_);
v___x_2709_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2708_);
v___x_2710_ = l_Lean_Syntax_isOfKind(v___x_2708_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
lean_dec(v___x_2708_);
lean_dec(v___x_2699_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v_a_2683_);
return v___x_2712_;
}
else
{
lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2713_ = l_Lean_Syntax_getArg(v___x_2708_, v___x_2693_);
v___x_2714_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2713_);
v___x_2715_ = l_Lean_Syntax_isOfKind(v___x_2713_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_dec(v___x_2713_);
lean_dec(v___x_2708_);
lean_dec(v___x_2699_);
v___x_2716_ = lean_box(0);
v___x_2717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_a_2683_);
return v___x_2717_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2718_ = l_Lean_Syntax_getArg(v___x_2713_, v___x_2688_);
lean_dec(v___x_2713_);
v___x_2719_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2718_);
v___x_2720_ = l_Lean_Syntax_isOfKind(v___x_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v___x_2718_);
lean_dec(v___x_2708_);
lean_dec(v___x_2699_);
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_a_2683_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2723_ = l_Lean_Syntax_getArg(v___x_2718_, v___x_2693_);
lean_dec(v___x_2718_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_Lean_Syntax_matchesIdent(v___x_2723_, v___x_2724_);
lean_dec(v___x_2723_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v___x_2708_);
lean_dec(v___x_2699_);
v___x_2726_ = lean_box(0);
v___x_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v_a_2683_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v___x_2728_ = l_Lean_Syntax_getArg(v___x_2708_, v___x_2688_);
v___x_2729_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2728_);
v___x_2730_ = l_Lean_Syntax_isOfKind(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_dec(v___x_2728_);
lean_dec(v___x_2708_);
lean_dec(v___x_2699_);
v___x_2731_ = lean_box(0);
v___x_2732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v_a_2683_);
return v___x_2732_;
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = lean_unsigned_to_nat(3u);
v___x_2734_ = l_Lean_Syntax_getArg(v___x_2708_, v___x_2733_);
lean_dec(v___x_2708_);
lean_inc(v___x_2734_);
v___x_2735_ = l_Lean_Syntax_matchesNull(v___x_2734_, v___x_2688_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v___x_2734_);
lean_dec(v___x_2728_);
lean_dec(v___x_2699_);
v___x_2736_ = lean_box(0);
v___x_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
lean_ctor_set(v___x_2737_, 1, v_a_2683_);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = l_Lean_Syntax_getArg(v___x_2699_, v___x_2688_);
v___x_2739_ = l_Lean_Syntax_matchesNull(v___x_2738_, v___x_2693_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec(v___x_2734_);
lean_dec(v___x_2728_);
lean_dec(v___x_2699_);
v___x_2740_ = lean_box(0);
v___x_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_a_2683_);
return v___x_2741_;
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; uint8_t v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2742_ = l_Lean_Syntax_getArg(v___x_2734_, v___x_2693_);
lean_dec(v___x_2734_);
v___x_2743_ = l_Lean_Syntax_getArg(v___x_2699_, v___x_2733_);
lean_dec(v___x_2699_);
v___x_2744_ = 0;
v___x_2745_ = l_Lean_SourceInfo_fromRef(v_a_2682_, v___x_2744_);
v___x_2746_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_2747_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2748_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2745_, 7);
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2751_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2752_ = l_Lean_Syntax_node1(v___x_2745_, v___x_2751_, v___x_2728_);
v___x_2753_ = l_Lean_Syntax_node1(v___x_2745_, v___x_2750_, v___x_2752_);
v___x_2754_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2745_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2745_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_node5(v___x_2745_, v___x_2747_, v___x_2749_, v___x_2753_, v___x_2755_, v___x_2742_, v___x_2757_);
v___x_2759_ = ((lean_object*)(l_unexpandSigma___closed__0));
v___x_2760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2745_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = l_Lean_Syntax_node3(v___x_2745_, v___x_2746_, v___x_2758_, v___x_2760_, v___x_2743_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_a_2683_);
return v___x_2762_;
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
LEAN_EXPORT lean_object* l_unexpandSigma___boxed(lean_object* v_x_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l_unexpandSigma(v_x_2763_, v_a_2764_, v_a_2765_);
lean_dec(v_a_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_unexpandPSigma(lean_object* v_x_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2768_);
v___x_2772_ = l_Lean_Syntax_isOfKind(v_x_2768_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
lean_dec(v_x_2768_);
v___x_2773_ = lean_box(0);
v___x_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2774_, 0, v___x_2773_);
lean_ctor_set(v___x_2774_, 1, v_a_2770_);
return v___x_2774_;
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = lean_unsigned_to_nat(1u);
v___x_2776_ = l_Lean_Syntax_getArg(v_x_2768_, v___x_2775_);
lean_dec(v_x_2768_);
lean_inc(v___x_2776_);
v___x_2777_ = l_Lean_Syntax_matchesNull(v___x_2776_, v___x_2775_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
lean_dec(v___x_2776_);
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v_a_2770_);
return v___x_2779_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v___x_2780_ = lean_unsigned_to_nat(0u);
v___x_2781_ = l_Lean_Syntax_getArg(v___x_2776_, v___x_2780_);
lean_dec(v___x_2776_);
v___x_2782_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2781_);
v___x_2783_ = l_Lean_Syntax_isOfKind(v___x_2781_, v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v___x_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v_a_2770_);
return v___x_2785_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v___x_2786_ = l_Lean_Syntax_getArg(v___x_2781_, v___x_2775_);
lean_dec(v___x_2781_);
v___x_2787_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2786_);
v___x_2788_ = l_Lean_Syntax_isOfKind(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec(v___x_2786_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v_a_2770_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; uint8_t v___x_2792_; 
v___x_2791_ = l_Lean_Syntax_getArg(v___x_2786_, v___x_2780_);
lean_inc(v___x_2791_);
v___x_2792_ = l_Lean_Syntax_matchesNull(v___x_2791_, v___x_2775_);
if (v___x_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v___x_2791_);
lean_dec(v___x_2786_);
v___x_2793_ = lean_box(0);
v___x_2794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
lean_ctor_set(v___x_2794_, 1, v_a_2770_);
return v___x_2794_;
}
else
{
lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v___x_2795_ = l_Lean_Syntax_getArg(v___x_2791_, v___x_2780_);
lean_dec(v___x_2791_);
v___x_2796_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2795_);
v___x_2797_ = l_Lean_Syntax_isOfKind(v___x_2795_, v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_dec(v___x_2795_);
lean_dec(v___x_2786_);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_a_2770_);
return v___x_2799_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2800_ = l_Lean_Syntax_getArg(v___x_2795_, v___x_2780_);
v___x_2801_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2800_);
v___x_2802_ = l_Lean_Syntax_isOfKind(v___x_2800_, v___x_2801_);
if (v___x_2802_ == 0)
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_dec(v___x_2800_);
lean_dec(v___x_2795_);
lean_dec(v___x_2786_);
v___x_2803_ = lean_box(0);
v___x_2804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
lean_ctor_set(v___x_2804_, 1, v_a_2770_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v___x_2805_ = l_Lean_Syntax_getArg(v___x_2800_, v___x_2775_);
lean_dec(v___x_2800_);
v___x_2806_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2805_);
v___x_2807_ = l_Lean_Syntax_isOfKind(v___x_2805_, v___x_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec(v___x_2805_);
lean_dec(v___x_2795_);
lean_dec(v___x_2786_);
v___x_2808_ = lean_box(0);
v___x_2809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v_a_2770_);
return v___x_2809_;
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = l_Lean_Syntax_getArg(v___x_2805_, v___x_2780_);
lean_dec(v___x_2805_);
v___x_2811_ = lean_box(0);
v___x_2812_ = l_Lean_Syntax_matchesIdent(v___x_2810_, v___x_2811_);
lean_dec(v___x_2810_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec(v___x_2795_);
lean_dec(v___x_2786_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_a_2770_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = l_Lean_Syntax_getArg(v___x_2795_, v___x_2775_);
v___x_2816_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2815_);
v___x_2817_ = l_Lean_Syntax_isOfKind(v___x_2815_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v___x_2815_);
lean_dec(v___x_2795_);
lean_dec(v___x_2786_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_a_2770_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2820_ = lean_unsigned_to_nat(3u);
v___x_2821_ = l_Lean_Syntax_getArg(v___x_2795_, v___x_2820_);
lean_dec(v___x_2795_);
lean_inc(v___x_2821_);
v___x_2822_ = l_Lean_Syntax_matchesNull(v___x_2821_, v___x_2775_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_dec(v___x_2821_);
lean_dec(v___x_2815_);
lean_dec(v___x_2786_);
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
lean_ctor_set(v___x_2824_, 1, v_a_2770_);
return v___x_2824_;
}
else
{
lean_object* v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = l_Lean_Syntax_getArg(v___x_2786_, v___x_2775_);
v___x_2826_ = l_Lean_Syntax_matchesNull(v___x_2825_, v___x_2780_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
lean_dec(v___x_2821_);
lean_dec(v___x_2815_);
lean_dec(v___x_2786_);
v___x_2827_ = lean_box(0);
v___x_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2827_);
lean_ctor_set(v___x_2828_, 1, v_a_2770_);
return v___x_2828_;
}
else
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2829_ = l_Lean_Syntax_getArg(v___x_2821_, v___x_2780_);
lean_dec(v___x_2821_);
v___x_2830_ = l_Lean_Syntax_getArg(v___x_2786_, v___x_2820_);
lean_dec(v___x_2786_);
v___x_2831_ = 0;
v___x_2832_ = l_Lean_SourceInfo_fromRef(v_a_2769_, v___x_2831_);
v___x_2833_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_2834_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2835_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2832_, 7);
v___x_2836_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2832_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2838_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2839_ = l_Lean_Syntax_node1(v___x_2832_, v___x_2838_, v___x_2815_);
v___x_2840_ = l_Lean_Syntax_node1(v___x_2832_, v___x_2837_, v___x_2839_);
v___x_2841_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2832_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2832_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = l_Lean_Syntax_node5(v___x_2832_, v___x_2834_, v___x_2836_, v___x_2840_, v___x_2842_, v___x_2829_, v___x_2844_);
v___x_2846_ = ((lean_object*)(l_unexpandPSigma___closed__0));
v___x_2847_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2832_);
lean_ctor_set(v___x_2847_, 1, v___x_2846_);
v___x_2848_ = l_Lean_Syntax_node3(v___x_2832_, v___x_2833_, v___x_2845_, v___x_2847_, v___x_2830_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2848_);
lean_ctor_set(v___x_2849_, 1, v_a_2770_);
return v___x_2849_;
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
LEAN_EXPORT lean_object* l_unexpandPSigma___boxed(lean_object* v_x_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_unexpandPSigma(v_x_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2851_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_unexpandSubtype(lean_object* v_x_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2860_);
v___x_2864_ = l_Lean_Syntax_isOfKind(v_x_2860_, v___x_2863_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
lean_dec(v_x_2860_);
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v_a_2862_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2867_ = lean_unsigned_to_nat(1u);
v___x_2868_ = l_Lean_Syntax_getArg(v_x_2860_, v___x_2867_);
lean_dec(v_x_2860_);
lean_inc(v___x_2868_);
v___x_2869_ = l_Lean_Syntax_matchesNull(v___x_2868_, v___x_2867_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec(v___x_2868_);
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_a_2862_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; uint8_t v___x_2875_; 
v___x_2872_ = lean_unsigned_to_nat(0u);
v___x_2873_ = l_Lean_Syntax_getArg(v___x_2868_, v___x_2872_);
lean_dec(v___x_2868_);
v___x_2874_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2873_);
v___x_2875_ = l_Lean_Syntax_isOfKind(v___x_2873_, v___x_2874_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_dec(v___x_2873_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
lean_ctor_set(v___x_2877_, 1, v_a_2862_);
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2878_ = l_Lean_Syntax_getArg(v___x_2873_, v___x_2867_);
lean_dec(v___x_2873_);
v___x_2879_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2878_);
v___x_2880_ = l_Lean_Syntax_isOfKind(v___x_2878_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v_a_2862_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; uint8_t v___x_2884_; 
v___x_2883_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2872_);
lean_inc(v___x_2883_);
v___x_2884_ = l_Lean_Syntax_matchesNull(v___x_2883_, v___x_2867_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec(v___x_2883_);
lean_dec(v___x_2878_);
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
lean_ctor_set(v___x_2886_, 1, v_a_2862_);
return v___x_2886_;
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = l_Lean_Syntax_getArg(v___x_2883_, v___x_2872_);
lean_dec(v___x_2883_);
v___x_2888_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2887_);
v___x_2889_ = l_Lean_Syntax_isOfKind(v___x_2887_, v___x_2888_);
if (v___x_2889_ == 0)
{
if (v___x_2889_ == 0)
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2887_);
v___x_2911_ = l_Lean_Syntax_isOfKind(v___x_2887_, v___x_2910_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2912_ = lean_box(0);
v___x_2913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2912_);
lean_ctor_set(v___x_2913_, 1, v_a_2862_);
return v___x_2913_;
}
else
{
goto v___jp_2890_;
}
}
else
{
goto v___jp_2890_;
}
}
else
{
lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2914_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2872_);
v___x_2915_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2914_);
v___x_2916_ = l_Lean_Syntax_isOfKind(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
lean_dec(v___x_2914_);
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_a_2862_);
return v___x_2918_;
}
else
{
lean_object* v___x_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; 
v___x_2919_ = l_Lean_Syntax_getArg(v___x_2914_, v___x_2867_);
lean_dec(v___x_2914_);
v___x_2920_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2919_);
v___x_2921_ = l_Lean_Syntax_isOfKind(v___x_2919_, v___x_2920_);
if (v___x_2921_ == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
lean_dec(v___x_2919_);
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
lean_ctor_set(v___x_2923_, 1, v_a_2862_);
return v___x_2923_;
}
else
{
lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v___x_2926_; 
v___x_2924_ = l_Lean_Syntax_getArg(v___x_2919_, v___x_2872_);
lean_dec(v___x_2919_);
v___x_2925_ = lean_box(0);
v___x_2926_ = l_Lean_Syntax_matchesIdent(v___x_2924_, v___x_2925_);
lean_dec(v___x_2924_);
if (v___x_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v_a_2862_);
return v___x_2928_;
}
else
{
lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2929_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2867_);
v___x_2930_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2929_);
v___x_2931_ = l_Lean_Syntax_isOfKind(v___x_2929_, v___x_2930_);
if (v___x_2931_ == 0)
{
lean_object* v___x_2932_; lean_object* v___x_2933_; 
lean_dec(v___x_2929_);
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2932_);
lean_ctor_set(v___x_2933_, 1, v_a_2862_);
return v___x_2933_;
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_unsigned_to_nat(3u);
v___x_2935_ = l_Lean_Syntax_getArg(v___x_2887_, v___x_2934_);
lean_dec(v___x_2887_);
lean_inc(v___x_2935_);
v___x_2936_ = l_Lean_Syntax_matchesNull(v___x_2935_, v___x_2867_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
lean_dec(v___x_2935_);
lean_dec(v___x_2929_);
lean_dec(v___x_2878_);
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2937_);
lean_ctor_set(v___x_2938_, 1, v_a_2862_);
return v___x_2938_;
}
else
{
lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2867_);
v___x_2940_ = l_Lean_Syntax_matchesNull(v___x_2939_, v___x_2872_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec(v___x_2935_);
lean_dec(v___x_2929_);
lean_dec(v___x_2878_);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_a_2862_);
return v___x_2942_;
}
else
{
lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2943_ = l_Lean_Syntax_getArg(v___x_2935_, v___x_2872_);
lean_dec(v___x_2935_);
v___x_2944_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2934_);
lean_dec(v___x_2878_);
v___x_2945_ = 0;
v___x_2946_ = l_Lean_SourceInfo_fromRef(v_a_2861_, v___x_2945_);
v___x_2947_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2948_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2946_, 5);
v___x_2949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2946_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2951_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2946_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = l_Lean_Syntax_node2(v___x_2946_, v___x_2950_, v___x_2952_, v___x_2943_);
v___x_2954_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2955_, 0, v___x_2946_);
lean_ctor_set(v___x_2955_, 1, v___x_2954_);
v___x_2956_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2946_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
v___x_2958_ = l_Lean_Syntax_node6(v___x_2946_, v___x_2947_, v___x_2949_, v___x_2929_, v___x_2953_, v___x_2955_, v___x_2944_, v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v_a_2862_);
return v___x_2959_;
}
}
}
}
}
}
}
v___jp_2890_:
{
lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2891_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2867_);
v___x_2892_ = l_Lean_Syntax_matchesNull(v___x_2891_, v___x_2872_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v___x_2887_);
lean_dec(v___x_2878_);
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
lean_ctor_set(v___x_2894_, 1, v_a_2862_);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2895_ = lean_unsigned_to_nat(3u);
v___x_2896_ = l_Lean_Syntax_getArg(v___x_2878_, v___x_2895_);
lean_dec(v___x_2878_);
v___x_2897_ = l_Lean_SourceInfo_fromRef(v_a_2861_, v___x_2889_);
v___x_2898_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2899_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2897_, 4);
v___x_2900_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2897_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
v___x_2901_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2902_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2897_);
lean_ctor_set(v___x_2903_, 1, v___x_2901_);
lean_ctor_set(v___x_2903_, 2, v___x_2902_);
v___x_2904_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2897_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2897_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = l_Lean_Syntax_node6(v___x_2897_, v___x_2898_, v___x_2900_, v___x_2887_, v___x_2903_, v___x_2905_, v___x_2896_, v___x_2907_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v_a_2862_);
return v___x_2909_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandSubtype___boxed(lean_object* v_x_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_unexpandSubtype(v_x_2960_, v_a_2961_, v_a_2962_);
lean_dec(v_a_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax(lean_object* v_x_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; 
v___x_2967_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2964_);
v___x_2968_ = l_Lean_Syntax_isOfKind(v_x_2964_, v___x_2967_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec(v_x_2964_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
lean_ctor_set(v___x_2970_, 1, v_a_2966_);
return v___x_2970_;
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = l_Lean_Syntax_getArg(v_x_2964_, v___x_2971_);
lean_inc(v___x_2972_);
v___x_2973_ = l_Lean_Syntax_matchesNull(v___x_2972_, v___x_2971_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___x_2972_);
lean_dec(v_x_2964_);
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v_a_2966_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2976_ = lean_unsigned_to_nat(0u);
v___x_2977_ = l_Lean_Syntax_getArg(v___x_2972_, v___x_2976_);
lean_dec(v___x_2972_);
v___x_2978_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2977_);
v___x_2979_ = l_Lean_Syntax_isOfKind(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v___x_2977_);
lean_dec(v_x_2964_);
v___x_2980_ = lean_box(0);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2980_);
lean_ctor_set(v___x_2981_, 1, v_a_2966_);
return v___x_2981_;
}
else
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = l_Lean_Syntax_getArg(v___x_2977_, v___x_2971_);
lean_dec(v___x_2977_);
lean_inc(v___x_2982_);
v___x_2983_ = l_Lean_Syntax_matchesNull(v___x_2982_, v___x_2971_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v___x_2982_);
lean_dec(v_x_2964_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
lean_ctor_set(v___x_2985_, 1, v_a_2966_);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2986_ = l_Lean_Syntax_getArg(v_x_2964_, v___x_2976_);
lean_dec(v_x_2964_);
v___x_2987_ = l_Lean_Syntax_getArg(v___x_2982_, v___x_2976_);
lean_dec(v___x_2982_);
v___x_2988_ = 0;
v___x_2989_ = l_Lean_SourceInfo_fromRef(v_a_2965_, v___x_2988_);
v___x_2990_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_2989_);
v___x_2991_ = l_Lean_Syntax_node1(v___x_2989_, v___x_2990_, v___x_2987_);
v___x_2992_ = l_Lean_Syntax_node2(v___x_2989_, v___x_2967_, v___x_2986_, v___x_2991_);
v___x_2993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v_a_2966_);
return v___x_2993_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax___boxed(lean_object* v_x_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_unexpandTSyntax(v_x_2994_, v_a_2995_, v_a_2996_);
lean_dec(v_a_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray(lean_object* v_x_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_){
_start:
{
lean_object* v___x_3001_; uint8_t v___x_3002_; 
v___x_3001_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2998_);
v___x_3002_ = l_Lean_Syntax_isOfKind(v_x_2998_, v___x_3001_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
lean_dec(v_x_2998_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
lean_ctor_set(v___x_3004_, 1, v_a_3000_);
return v___x_3004_;
}
else
{
lean_object* v___x_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v___x_3005_ = lean_unsigned_to_nat(1u);
v___x_3006_ = l_Lean_Syntax_getArg(v_x_2998_, v___x_3005_);
lean_inc(v___x_3006_);
v___x_3007_ = l_Lean_Syntax_matchesNull(v___x_3006_, v___x_3005_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v___x_3006_);
lean_dec(v_x_2998_);
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
lean_ctor_set(v___x_3009_, 1, v_a_3000_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = l_Lean_Syntax_getArg(v___x_3006_, v___x_3010_);
lean_dec(v___x_3006_);
v___x_3012_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_3011_);
v___x_3013_ = l_Lean_Syntax_isOfKind(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
lean_dec(v___x_3011_);
lean_dec(v_x_2998_);
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_a_3000_);
return v___x_3015_;
}
else
{
lean_object* v___x_3016_; uint8_t v___x_3017_; 
v___x_3016_ = l_Lean_Syntax_getArg(v___x_3011_, v___x_3005_);
lean_dec(v___x_3011_);
lean_inc(v___x_3016_);
v___x_3017_ = l_Lean_Syntax_matchesNull(v___x_3016_, v___x_3005_);
if (v___x_3017_ == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v___x_3016_);
lean_dec(v_x_2998_);
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v_a_3000_);
return v___x_3019_;
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3020_ = l_Lean_Syntax_getArg(v_x_2998_, v___x_3010_);
lean_dec(v_x_2998_);
v___x_3021_ = l_Lean_Syntax_getArg(v___x_3016_, v___x_3010_);
lean_dec(v___x_3016_);
v___x_3022_ = 0;
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_a_2999_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3023_);
v___x_3025_ = l_Lean_Syntax_node1(v___x_3023_, v___x_3024_, v___x_3021_);
v___x_3026_ = l_Lean_Syntax_node2(v___x_3023_, v___x_3001_, v___x_3020_, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v_a_3000_);
return v___x_3027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray___boxed(lean_object* v_x_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_unexpandTSyntaxArray(v_x_3028_, v_a_3029_, v_a_3030_);
lean_dec(v_a_3029_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray(lean_object* v_x_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3035_; uint8_t v___x_3036_; 
v___x_3035_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3032_);
v___x_3036_ = l_Lean_Syntax_isOfKind(v_x_3032_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_dec(v_x_3032_);
v___x_3037_ = lean_box(0);
v___x_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3037_);
lean_ctor_set(v___x_3038_, 1, v_a_3034_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3039_ = lean_unsigned_to_nat(1u);
v___x_3040_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3039_);
v___x_3041_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3040_);
v___x_3042_ = l_Lean_Syntax_matchesNull(v___x_3040_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
lean_dec(v___x_3040_);
lean_dec(v_x_3032_);
v___x_3043_ = lean_box(0);
v___x_3044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3043_);
lean_ctor_set(v___x_3044_, 1, v_a_3034_);
return v___x_3044_;
}
else
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = l_Lean_Syntax_getArg(v___x_3040_, v___x_3045_);
v___x_3047_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_3046_);
v___x_3048_ = l_Lean_Syntax_isOfKind(v___x_3046_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec(v___x_3046_);
lean_dec(v___x_3040_);
lean_dec(v_x_3032_);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v_a_3034_);
return v___x_3050_;
}
else
{
lean_object* v___x_3051_; uint8_t v___x_3052_; 
v___x_3051_ = l_Lean_Syntax_getArg(v___x_3046_, v___x_3039_);
lean_dec(v___x_3046_);
lean_inc(v___x_3051_);
v___x_3052_ = l_Lean_Syntax_matchesNull(v___x_3051_, v___x_3039_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec(v___x_3051_);
lean_dec(v___x_3040_);
lean_dec(v_x_3032_);
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v_a_3034_);
return v___x_3054_;
}
else
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3055_ = l_Lean_Syntax_getArg(v_x_3032_, v___x_3045_);
lean_dec(v_x_3032_);
v___x_3056_ = l_Lean_Syntax_getArg(v___x_3051_, v___x_3045_);
lean_dec(v___x_3051_);
v___x_3057_ = l_Lean_Syntax_getArg(v___x_3040_, v___x_3039_);
lean_dec(v___x_3040_);
v___x_3058_ = 0;
v___x_3059_ = l_Lean_SourceInfo_fromRef(v_a_3033_, v___x_3058_);
v___x_3060_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3059_);
v___x_3061_ = l_Lean_Syntax_node2(v___x_3059_, v___x_3060_, v___x_3056_, v___x_3057_);
v___x_3062_ = l_Lean_Syntax_node2(v___x_3059_, v___x_3035_, v___x_3055_, v___x_3061_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
lean_ctor_set(v___x_3063_, 1, v_a_3034_);
return v___x_3063_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray___boxed(lean_object* v_x_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_unexpandTSepArray(v_x_3064_, v_a_3065_, v_a_3066_);
lean_dec(v_a_3065_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem(lean_object* v_x_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_){
_start:
{
lean_object* v___x_3074_; uint8_t v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3071_);
v___x_3075_ = l_Lean_Syntax_isOfKind(v_x_3071_, v___x_3074_);
if (v___x_3075_ == 0)
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
lean_dec(v_x_3071_);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v_a_3073_);
return v___x_3077_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v___x_3078_ = lean_unsigned_to_nat(1u);
v___x_3079_ = l_Lean_Syntax_getArg(v_x_3071_, v___x_3078_);
lean_dec(v_x_3071_);
v___x_3080_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3079_);
v___x_3081_ = l_Lean_Syntax_matchesNull(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v_a_3073_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3084_ = lean_unsigned_to_nat(0u);
v___x_3085_ = l_Lean_Syntax_getArg(v___x_3079_, v___x_3084_);
v___x_3086_ = l_Lean_Syntax_getArg(v___x_3079_, v___x_3078_);
lean_dec(v___x_3079_);
v___x_3087_ = 0;
v___x_3088_ = l_Lean_SourceInfo_fromRef(v_a_3072_, v___x_3087_);
v___x_3089_ = ((lean_object*)(l_unexpandGetElem___closed__1));
v___x_3090_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_3088_, 2);
v___x_3091_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3088_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v___x_3092_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3088_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = l_Lean_Syntax_node4(v___x_3088_, v___x_3089_, v___x_3085_, v___x_3091_, v___x_3086_, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_a_3073_);
return v___x_3095_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem___boxed(lean_object* v_x_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_unexpandGetElem(v_x_3096_, v_a_3097_, v_a_3098_);
lean_dec(v_a_3097_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21(lean_object* v_x_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3104_);
v___x_3108_ = l_Lean_Syntax_isOfKind(v_x_3104_, v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_dec(v_x_3104_);
v___x_3109_ = lean_box(0);
v___x_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v_a_3106_);
return v___x_3110_;
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = l_Lean_Syntax_getArg(v_x_3104_, v___x_3111_);
lean_dec(v_x_3104_);
v___x_3113_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3112_);
v___x_3114_ = l_Lean_Syntax_matchesNull(v___x_3112_, v___x_3113_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v_a_3106_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = l_Lean_Syntax_getArg(v___x_3112_, v___x_3117_);
v___x_3119_ = l_Lean_Syntax_getArg(v___x_3112_, v___x_3111_);
lean_dec(v___x_3112_);
v___x_3120_ = 0;
v___x_3121_ = l_Lean_SourceInfo_fromRef(v_a_3105_, v___x_3120_);
v___x_3122_ = ((lean_object*)(l_unexpandGetElem_x21___closed__1));
v___x_3123_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_3124_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_3121_, 4);
v___x_3125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3121_);
lean_ctor_set(v___x_3125_, 1, v___x_3123_);
lean_ctor_set(v___x_3125_, 2, v___x_3124_);
v___x_3126_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_3127_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3121_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3121_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
v___x_3130_ = ((lean_object*)(l_unexpandGetElem_x21___closed__2));
v___x_3131_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3121_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
lean_inc_ref(v___x_3125_);
v___x_3132_ = l_Lean_Syntax_node7(v___x_3121_, v___x_3122_, v___x_3118_, v___x_3125_, v___x_3127_, v___x_3119_, v___x_3129_, v___x_3125_, v___x_3131_);
v___x_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v_a_3106_);
return v___x_3133_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21___boxed(lean_object* v_x_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_unexpandGetElem_x21(v_x_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f(lean_object* v_x_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_){
_start:
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3142_);
v___x_3146_ = l_Lean_Syntax_isOfKind(v_x_3142_, v___x_3145_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
lean_dec(v_x_3142_);
v___x_3147_ = lean_box(0);
v___x_3148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3148_, 0, v___x_3147_);
lean_ctor_set(v___x_3148_, 1, v_a_3144_);
return v___x_3148_;
}
else
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; uint8_t v___x_3152_; 
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = l_Lean_Syntax_getArg(v_x_3142_, v___x_3149_);
lean_dec(v_x_3142_);
v___x_3151_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3150_);
v___x_3152_ = l_Lean_Syntax_matchesNull(v___x_3150_, v___x_3151_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v___x_3154_; 
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v___x_3154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3153_);
lean_ctor_set(v___x_3154_, 1, v_a_3144_);
return v___x_3154_;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3155_ = lean_unsigned_to_nat(0u);
v___x_3156_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_3155_);
v___x_3157_ = l_Lean_Syntax_getArg(v___x_3150_, v___x_3149_);
lean_dec(v___x_3150_);
v___x_3158_ = 0;
v___x_3159_ = l_Lean_SourceInfo_fromRef(v_a_3143_, v___x_3158_);
v___x_3160_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__1));
v___x_3161_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_3162_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_3159_, 4);
v___x_3163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3159_);
lean_ctor_set(v___x_3163_, 1, v___x_3161_);
lean_ctor_set(v___x_3163_, 2, v___x_3162_);
v___x_3164_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_3165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3159_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3167_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3159_);
lean_ctor_set(v___x_3167_, 1, v___x_3166_);
v___x_3168_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__2));
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3159_);
lean_ctor_set(v___x_3169_, 1, v___x_3168_);
lean_inc_ref(v___x_3163_);
v___x_3170_ = l_Lean_Syntax_node7(v___x_3159_, v___x_3160_, v___x_3156_, v___x_3163_, v___x_3165_, v___x_3157_, v___x_3167_, v___x_3163_, v___x_3169_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3170_);
lean_ctor_set(v___x_3171_, 1, v_a_3144_);
return v___x_3171_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f___boxed(lean_object* v_x_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_unexpandGetElem_x3f(v_x_3172_, v_a_3173_, v_a_3174_);
lean_dec(v_a_3173_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg(lean_object* v_a_3176_, lean_object* v_a_3177_){
_start:
{
uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3178_ = 0;
v___x_3179_ = l_Lean_SourceInfo_fromRef(v_a_3176_, v___x_3178_);
v___x_3180_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3181_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3179_, 3);
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
v___x_3183_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3184_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3179_);
lean_ctor_set(v___x_3185_, 1, v___x_3183_);
lean_ctor_set(v___x_3185_, 2, v___x_3184_);
v___x_3186_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3179_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = l_Lean_Syntax_node3(v___x_3179_, v___x_3180_, v___x_3182_, v___x_3185_, v___x_3187_);
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v_a_3177_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg___boxed(lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_unexpandArrayEmpty___redArg(v_a_3190_, v_a_3191_);
lean_dec(v_a_3190_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty(lean_object* v_x_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_unexpandArrayEmpty___redArg(v_a_3194_, v_a_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___boxed(lean_object* v_x_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_){
_start:
{
lean_object* v_res_3200_; 
v_res_3200_ = l_unexpandArrayEmpty(v_x_3197_, v_a_3198_, v_a_3199_);
lean_dec(v_a_3198_);
lean_dec(v_x_3197_);
return v_res_3200_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg(lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
uint8_t v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3203_ = 0;
v___x_3204_ = l_Lean_SourceInfo_fromRef(v_a_3201_, v___x_3203_);
v___x_3205_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3206_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3204_, 3);
v___x_3207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3204_);
lean_ctor_set(v___x_3207_, 1, v___x_3206_);
v___x_3208_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3209_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3204_);
lean_ctor_set(v___x_3210_, 1, v___x_3208_);
lean_ctor_set(v___x_3210_, 2, v___x_3209_);
v___x_3211_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3204_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_Syntax_node3(v___x_3204_, v___x_3205_, v___x_3207_, v___x_3210_, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
lean_ctor_set(v___x_3214_, 1, v_a_3202_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg___boxed(lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_unexpandMkArray0___redArg(v_a_3215_, v_a_3216_);
lean_dec(v_a_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0(lean_object* v_x_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_unexpandMkArray0___redArg(v_a_3219_, v_a_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___boxed(lean_object* v_x_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_unexpandMkArray0(v_x_3222_, v_a_3223_, v_a_3224_);
lean_dec(v_a_3223_);
lean_dec(v_x_3222_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1(lean_object* v_x_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3226_);
v___x_3230_ = l_Lean_Syntax_isOfKind(v_x_3226_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_x_3226_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v_a_3228_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3233_ = lean_unsigned_to_nat(1u);
v___x_3234_ = l_Lean_Syntax_getArg(v_x_3226_, v___x_3233_);
lean_dec(v_x_3226_);
lean_inc(v___x_3234_);
v___x_3235_ = l_Lean_Syntax_matchesNull(v___x_3234_, v___x_3233_);
if (v___x_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec(v___x_3234_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3236_);
lean_ctor_set(v___x_3237_, 1, v_a_3228_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l_Lean_Syntax_getArg(v___x_3234_, v___x_3238_);
lean_dec(v___x_3234_);
v___x_3240_ = 0;
v___x_3241_ = l_Lean_SourceInfo_fromRef(v_a_3227_, v___x_3240_);
v___x_3242_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3243_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3241_, 3);
v___x_3244_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3241_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
v___x_3245_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3246_ = l_Lean_Syntax_node1(v___x_3241_, v___x_3245_, v___x_3239_);
v___x_3247_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3241_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = l_Lean_Syntax_node3(v___x_3241_, v___x_3242_, v___x_3244_, v___x_3246_, v___x_3248_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3249_);
lean_ctor_set(v___x_3250_, 1, v_a_3228_);
return v___x_3250_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1___boxed(lean_object* v_x_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_unexpandMkArray1(v_x_3251_, v_a_3252_, v_a_3253_);
lean_dec(v_a_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2(lean_object* v_x_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_){
_start:
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3255_);
v___x_3259_ = l_Lean_Syntax_isOfKind(v_x_3255_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_x_3255_);
v___x_3260_ = lean_box(0);
v___x_3261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3260_);
lean_ctor_set(v___x_3261_, 1, v_a_3257_);
return v___x_3261_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3262_ = lean_unsigned_to_nat(1u);
v___x_3263_ = l_Lean_Syntax_getArg(v_x_3255_, v___x_3262_);
lean_dec(v_x_3255_);
v___x_3264_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3263_);
v___x_3265_ = l_Lean_Syntax_matchesNull(v___x_3263_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
lean_dec(v___x_3263_);
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v_a_3257_);
return v___x_3267_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3268_ = lean_unsigned_to_nat(0u);
v___x_3269_ = l_Lean_Syntax_getArg(v___x_3263_, v___x_3268_);
v___x_3270_ = l_Lean_Syntax_getArg(v___x_3263_, v___x_3262_);
lean_dec(v___x_3263_);
v___x_3271_ = 0;
v___x_3272_ = l_Lean_SourceInfo_fromRef(v_a_3256_, v___x_3271_);
v___x_3273_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3274_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3272_, 4);
v___x_3275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3272_);
lean_ctor_set(v___x_3275_, 1, v___x_3274_);
v___x_3276_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3277_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3272_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_Syntax_node3(v___x_3272_, v___x_3276_, v___x_3269_, v___x_3278_, v___x_3270_);
v___x_3280_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3281_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3272_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = l_Lean_Syntax_node3(v___x_3272_, v___x_3273_, v___x_3275_, v___x_3279_, v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v_a_3257_);
return v___x_3283_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2___boxed(lean_object* v_x_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_unexpandMkArray2(v_x_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3(lean_object* v_x_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_){
_start:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3288_);
v___x_3292_ = l_Lean_Syntax_isOfKind(v_x_3288_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_x_3288_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v_a_3290_);
return v___x_3294_;
}
else
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3295_ = lean_unsigned_to_nat(1u);
v___x_3296_ = l_Lean_Syntax_getArg(v_x_3288_, v___x_3295_);
lean_dec(v_x_3288_);
v___x_3297_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3296_);
v___x_3298_ = l_Lean_Syntax_matchesNull(v___x_3296_, v___x_3297_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v_a_3290_);
return v___x_3300_;
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3301_ = lean_unsigned_to_nat(0u);
v___x_3302_ = l_Lean_Syntax_getArg(v___x_3296_, v___x_3301_);
v___x_3303_ = l_Lean_Syntax_getArg(v___x_3296_, v___x_3295_);
v___x_3304_ = lean_unsigned_to_nat(2u);
v___x_3305_ = l_Lean_Syntax_getArg(v___x_3296_, v___x_3304_);
lean_dec(v___x_3296_);
v___x_3306_ = 0;
v___x_3307_ = l_Lean_SourceInfo_fromRef(v_a_3289_, v___x_3306_);
v___x_3308_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3309_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3307_, 4);
v___x_3310_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3307_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3312_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3313_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3307_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
lean_inc_ref(v___x_3313_);
v___x_3314_ = l_Lean_Syntax_node5(v___x_3307_, v___x_3311_, v___x_3302_, v___x_3313_, v___x_3303_, v___x_3313_, v___x_3305_);
v___x_3315_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3307_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_Syntax_node3(v___x_3307_, v___x_3308_, v___x_3310_, v___x_3314_, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v_a_3290_);
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3___boxed(lean_object* v_x_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_unexpandMkArray3(v_x_3319_, v_a_3320_, v_a_3321_);
lean_dec(v_a_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4(lean_object* v_x_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3326_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3323_);
v___x_3327_ = l_Lean_Syntax_isOfKind(v_x_3323_, v___x_3326_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
lean_dec(v_x_3323_);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_a_3325_);
return v___x_3329_;
}
else
{
lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3330_ = lean_unsigned_to_nat(1u);
v___x_3331_ = l_Lean_Syntax_getArg(v_x_3323_, v___x_3330_);
lean_dec(v_x_3323_);
v___x_3332_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_3331_);
v___x_3333_ = l_Lean_Syntax_matchesNull(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v___x_3335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v_a_3325_);
return v___x_3335_;
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3336_);
v___x_3338_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3330_);
v___x_3339_ = lean_unsigned_to_nat(2u);
v___x_3340_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3339_);
v___x_3341_ = lean_unsigned_to_nat(3u);
v___x_3342_ = l_Lean_Syntax_getArg(v___x_3331_, v___x_3341_);
lean_dec(v___x_3331_);
v___x_3343_ = 0;
v___x_3344_ = l_Lean_SourceInfo_fromRef(v_a_3324_, v___x_3343_);
v___x_3345_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3346_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3344_, 4);
v___x_3347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3349_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3344_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
lean_inc_ref_n(v___x_3350_, 2);
v___x_3351_ = l_Lean_Syntax_node7(v___x_3344_, v___x_3348_, v___x_3337_, v___x_3350_, v___x_3338_, v___x_3350_, v___x_3340_, v___x_3350_, v___x_3342_);
v___x_3352_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3344_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_Syntax_node3(v___x_3344_, v___x_3345_, v___x_3347_, v___x_3351_, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
lean_ctor_set(v___x_3355_, 1, v_a_3325_);
return v___x_3355_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4___boxed(lean_object* v_x_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l_unexpandMkArray4(v_x_3356_, v_a_3357_, v_a_3358_);
lean_dec(v_a_3357_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5(lean_object* v_x_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_){
_start:
{
lean_object* v___x_3363_; uint8_t v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3360_);
v___x_3364_ = l_Lean_Syntax_isOfKind(v_x_3360_, v___x_3363_);
if (v___x_3364_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec(v_x_3360_);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
lean_ctor_set(v___x_3366_, 1, v_a_3362_);
return v___x_3366_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3367_ = lean_unsigned_to_nat(1u);
v___x_3368_ = l_Lean_Syntax_getArg(v_x_3360_, v___x_3367_);
lean_dec(v_x_3360_);
v___x_3369_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3368_);
v___x_3370_ = l_Lean_Syntax_matchesNull(v___x_3368_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec(v___x_3368_);
v___x_3371_ = lean_box(0);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_a_3362_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3373_ = lean_unsigned_to_nat(0u);
v___x_3374_ = l_Lean_Syntax_getArg(v___x_3368_, v___x_3373_);
v___x_3375_ = l_Lean_Syntax_getArg(v___x_3368_, v___x_3367_);
v___x_3376_ = lean_unsigned_to_nat(2u);
v___x_3377_ = l_Lean_Syntax_getArg(v___x_3368_, v___x_3376_);
v___x_3378_ = lean_unsigned_to_nat(3u);
v___x_3379_ = l_Lean_Syntax_getArg(v___x_3368_, v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(4u);
v___x_3381_ = l_Lean_Syntax_getArg(v___x_3368_, v___x_3380_);
lean_dec(v___x_3368_);
v___x_3382_ = 0;
v___x_3383_ = l_Lean_SourceInfo_fromRef(v_a_3361_, v___x_3382_);
v___x_3384_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3385_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3383_, 4);
v___x_3386_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3383_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3388_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3383_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_unsigned_to_nat(9u);
v___x_3391_ = lean_mk_empty_array_with_capacity(v___x_3390_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3374_);
lean_inc_ref_n(v___x_3389_, 3);
v___x_3393_ = lean_array_push(v___x_3392_, v___x_3389_);
v___x_3394_ = lean_array_push(v___x_3393_, v___x_3375_);
v___x_3395_ = lean_array_push(v___x_3394_, v___x_3389_);
v___x_3396_ = lean_array_push(v___x_3395_, v___x_3377_);
v___x_3397_ = lean_array_push(v___x_3396_, v___x_3389_);
v___x_3398_ = lean_array_push(v___x_3397_, v___x_3379_);
v___x_3399_ = lean_array_push(v___x_3398_, v___x_3389_);
v___x_3400_ = lean_array_push(v___x_3399_, v___x_3381_);
v___x_3401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3383_);
lean_ctor_set(v___x_3401_, 1, v___x_3387_);
lean_ctor_set(v___x_3401_, 2, v___x_3400_);
v___x_3402_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3383_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = l_Lean_Syntax_node3(v___x_3383_, v___x_3384_, v___x_3386_, v___x_3401_, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3404_);
lean_ctor_set(v___x_3405_, 1, v_a_3362_);
return v___x_3405_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5___boxed(lean_object* v_x_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_unexpandMkArray5(v_x_3406_, v_a_3407_, v_a_3408_);
lean_dec(v_a_3407_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6(lean_object* v_x_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; uint8_t v___x_3414_; 
v___x_3413_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3410_);
v___x_3414_ = l_Lean_Syntax_isOfKind(v_x_3410_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v_x_3410_);
v___x_3415_ = lean_box(0);
v___x_3416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v_a_3412_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3417_ = lean_unsigned_to_nat(1u);
v___x_3418_ = l_Lean_Syntax_getArg(v_x_3410_, v___x_3417_);
lean_dec(v_x_3410_);
v___x_3419_ = lean_unsigned_to_nat(6u);
lean_inc(v___x_3418_);
v___x_3420_ = l_Lean_Syntax_matchesNull(v___x_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec(v___x_3418_);
v___x_3421_ = lean_box(0);
v___x_3422_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v_a_3412_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3423_ = lean_unsigned_to_nat(0u);
v___x_3424_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3423_);
v___x_3425_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3417_);
v___x_3426_ = lean_unsigned_to_nat(2u);
v___x_3427_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3426_);
v___x_3428_ = lean_unsigned_to_nat(3u);
v___x_3429_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3428_);
v___x_3430_ = lean_unsigned_to_nat(4u);
v___x_3431_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3430_);
v___x_3432_ = lean_unsigned_to_nat(5u);
v___x_3433_ = l_Lean_Syntax_getArg(v___x_3418_, v___x_3432_);
lean_dec(v___x_3418_);
v___x_3434_ = 0;
v___x_3435_ = l_Lean_SourceInfo_fromRef(v_a_3411_, v___x_3434_);
v___x_3436_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3437_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3435_, 4);
v___x_3438_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3435_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3440_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3441_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3435_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
v___x_3442_ = lean_unsigned_to_nat(11u);
v___x_3443_ = lean_mk_empty_array_with_capacity(v___x_3442_);
v___x_3444_ = lean_array_push(v___x_3443_, v___x_3424_);
lean_inc_ref_n(v___x_3441_, 4);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3441_);
v___x_3446_ = lean_array_push(v___x_3445_, v___x_3425_);
v___x_3447_ = lean_array_push(v___x_3446_, v___x_3441_);
v___x_3448_ = lean_array_push(v___x_3447_, v___x_3427_);
v___x_3449_ = lean_array_push(v___x_3448_, v___x_3441_);
v___x_3450_ = lean_array_push(v___x_3449_, v___x_3429_);
v___x_3451_ = lean_array_push(v___x_3450_, v___x_3441_);
v___x_3452_ = lean_array_push(v___x_3451_, v___x_3431_);
v___x_3453_ = lean_array_push(v___x_3452_, v___x_3441_);
v___x_3454_ = lean_array_push(v___x_3453_, v___x_3433_);
v___x_3455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3435_);
lean_ctor_set(v___x_3455_, 1, v___x_3439_);
lean_ctor_set(v___x_3455_, 2, v___x_3454_);
v___x_3456_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3435_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_Syntax_node3(v___x_3435_, v___x_3436_, v___x_3438_, v___x_3455_, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3458_);
lean_ctor_set(v___x_3459_, 1, v_a_3412_);
return v___x_3459_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6___boxed(lean_object* v_x_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v_res_3463_; 
v_res_3463_ = l_unexpandMkArray6(v_x_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_a_3461_);
return v_res_3463_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7(lean_object* v_x_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3467_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3464_);
v___x_3468_ = l_Lean_Syntax_isOfKind(v_x_3464_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec(v_x_3464_);
v___x_3469_ = lean_box(0);
v___x_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v_a_3466_);
return v___x_3470_;
}
else
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3471_ = lean_unsigned_to_nat(1u);
v___x_3472_ = l_Lean_Syntax_getArg(v_x_3464_, v___x_3471_);
lean_dec(v_x_3464_);
v___x_3473_ = lean_unsigned_to_nat(7u);
lean_inc(v___x_3472_);
v___x_3474_ = l_Lean_Syntax_matchesNull(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
lean_ctor_set(v___x_3476_, 1, v_a_3466_);
return v___x_3476_;
}
else
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3477_);
v___x_3479_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3471_);
v___x_3480_ = lean_unsigned_to_nat(2u);
v___x_3481_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3480_);
v___x_3482_ = lean_unsigned_to_nat(3u);
v___x_3483_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3482_);
v___x_3484_ = lean_unsigned_to_nat(4u);
v___x_3485_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3484_);
v___x_3486_ = lean_unsigned_to_nat(5u);
v___x_3487_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3486_);
v___x_3488_ = lean_unsigned_to_nat(6u);
v___x_3489_ = l_Lean_Syntax_getArg(v___x_3472_, v___x_3488_);
lean_dec(v___x_3472_);
v___x_3490_ = 0;
v___x_3491_ = l_Lean_SourceInfo_fromRef(v_a_3465_, v___x_3490_);
v___x_3492_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3493_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3491_, 4);
v___x_3494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3491_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
v___x_3495_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3496_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3491_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_unsigned_to_nat(13u);
v___x_3499_ = lean_mk_empty_array_with_capacity(v___x_3498_);
v___x_3500_ = lean_array_push(v___x_3499_, v___x_3478_);
lean_inc_ref_n(v___x_3497_, 5);
v___x_3501_ = lean_array_push(v___x_3500_, v___x_3497_);
v___x_3502_ = lean_array_push(v___x_3501_, v___x_3479_);
v___x_3503_ = lean_array_push(v___x_3502_, v___x_3497_);
v___x_3504_ = lean_array_push(v___x_3503_, v___x_3481_);
v___x_3505_ = lean_array_push(v___x_3504_, v___x_3497_);
v___x_3506_ = lean_array_push(v___x_3505_, v___x_3483_);
v___x_3507_ = lean_array_push(v___x_3506_, v___x_3497_);
v___x_3508_ = lean_array_push(v___x_3507_, v___x_3485_);
v___x_3509_ = lean_array_push(v___x_3508_, v___x_3497_);
v___x_3510_ = lean_array_push(v___x_3509_, v___x_3487_);
v___x_3511_ = lean_array_push(v___x_3510_, v___x_3497_);
v___x_3512_ = lean_array_push(v___x_3511_, v___x_3489_);
v___x_3513_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3491_);
lean_ctor_set(v___x_3513_, 1, v___x_3495_);
lean_ctor_set(v___x_3513_, 2, v___x_3512_);
v___x_3514_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3515_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3491_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = l_Lean_Syntax_node3(v___x_3491_, v___x_3492_, v___x_3494_, v___x_3513_, v___x_3515_);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v_a_3466_);
return v___x_3517_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7___boxed(lean_object* v_x_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l_unexpandMkArray7(v_x_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3519_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8(lean_object* v_x_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___x_3525_; uint8_t v___x_3526_; 
v___x_3525_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3522_);
v___x_3526_ = l_Lean_Syntax_isOfKind(v_x_3522_, v___x_3525_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_dec(v_x_3522_);
v___x_3527_ = lean_box(0);
v___x_3528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
lean_ctor_set(v___x_3528_, 1, v_a_3524_);
return v___x_3528_;
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; uint8_t v___x_3532_; 
v___x_3529_ = lean_unsigned_to_nat(1u);
v___x_3530_ = l_Lean_Syntax_getArg(v_x_3522_, v___x_3529_);
lean_dec(v_x_3522_);
v___x_3531_ = lean_unsigned_to_nat(8u);
lean_inc(v___x_3530_);
v___x_3532_ = l_Lean_Syntax_matchesNull(v___x_3530_, v___x_3531_);
if (v___x_3532_ == 0)
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v___x_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v_a_3524_);
return v___x_3534_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3535_ = lean_unsigned_to_nat(0u);
v___x_3536_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3535_);
v___x_3537_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3529_);
v___x_3538_ = lean_unsigned_to_nat(2u);
v___x_3539_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3538_);
v___x_3540_ = lean_unsigned_to_nat(3u);
v___x_3541_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3540_);
v___x_3542_ = lean_unsigned_to_nat(4u);
v___x_3543_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3542_);
v___x_3544_ = lean_unsigned_to_nat(5u);
v___x_3545_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3544_);
v___x_3546_ = lean_unsigned_to_nat(6u);
v___x_3547_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3546_);
v___x_3548_ = lean_unsigned_to_nat(7u);
v___x_3549_ = l_Lean_Syntax_getArg(v___x_3530_, v___x_3548_);
lean_dec(v___x_3530_);
v___x_3550_ = 0;
v___x_3551_ = l_Lean_SourceInfo_fromRef(v_a_3523_, v___x_3550_);
v___x_3552_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3553_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3551_, 4);
v___x_3554_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3551_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3556_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3557_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3551_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = lean_unsigned_to_nat(15u);
v___x_3559_ = lean_mk_empty_array_with_capacity(v___x_3558_);
v___x_3560_ = lean_array_push(v___x_3559_, v___x_3536_);
lean_inc_ref_n(v___x_3557_, 6);
v___x_3561_ = lean_array_push(v___x_3560_, v___x_3557_);
v___x_3562_ = lean_array_push(v___x_3561_, v___x_3537_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3557_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3539_);
v___x_3565_ = lean_array_push(v___x_3564_, v___x_3557_);
v___x_3566_ = lean_array_push(v___x_3565_, v___x_3541_);
v___x_3567_ = lean_array_push(v___x_3566_, v___x_3557_);
v___x_3568_ = lean_array_push(v___x_3567_, v___x_3543_);
v___x_3569_ = lean_array_push(v___x_3568_, v___x_3557_);
v___x_3570_ = lean_array_push(v___x_3569_, v___x_3545_);
v___x_3571_ = lean_array_push(v___x_3570_, v___x_3557_);
v___x_3572_ = lean_array_push(v___x_3571_, v___x_3547_);
v___x_3573_ = lean_array_push(v___x_3572_, v___x_3557_);
v___x_3574_ = lean_array_push(v___x_3573_, v___x_3549_);
v___x_3575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3551_);
lean_ctor_set(v___x_3575_, 1, v___x_3555_);
lean_ctor_set(v___x_3575_, 2, v___x_3574_);
v___x_3576_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3551_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = l_Lean_Syntax_node3(v___x_3551_, v___x_3552_, v___x_3554_, v___x_3575_, v___x_3577_);
v___x_3579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3578_);
lean_ctor_set(v___x_3579_, 1, v_a_3524_);
return v___x_3579_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8___boxed(lean_object* v_x_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_){
_start:
{
lean_object* v_res_3583_; 
v_res_3583_ = l_unexpandMkArray8(v_x_3580_, v_a_3581_, v_a_3582_);
lean_dec(v_a_3581_);
return v_res_3583_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3632_ = l_String_toRawSubstring_x27(v___x_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1(lean_object* v_x_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3664_ = ((lean_object*)(l_tacticFunext_______00__closed__1));
lean_inc(v_x_3661_);
v___x_3665_ = l_Lean_Syntax_isOfKind(v_x_3661_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
lean_dec(v_x_3661_);
v___x_3666_ = lean_box(1);
v___x_3667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v_a_3663_);
return v___x_3667_;
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3668_ = lean_unsigned_to_nat(0u);
v___x_3669_ = lean_unsigned_to_nat(1u);
v___x_3670_ = l_Lean_Syntax_getArg(v_x_3661_, v___x_3669_);
lean_dec(v_x_3661_);
lean_inc(v___x_3670_);
v___x_3671_ = l_Lean_Syntax_matchesNull(v___x_3670_, v___x_3668_);
if (v___x_3671_ == 0)
{
uint8_t v___x_3672_; 
lean_inc(v___x_3670_);
v___x_3672_ = l_Lean_Syntax_matchesNull(v___x_3670_, v___x_3669_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3673_ = l_Lean_Syntax_getNumArgs(v___x_3670_);
v___x_3674_ = lean_nat_dec_le(v___x_3669_, v___x_3673_);
if (v___x_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec(v___x_3673_);
lean_dec(v___x_3670_);
v___x_3675_ = lean_box(1);
v___x_3676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
lean_ctor_set(v___x_3676_, 1, v_a_3663_);
return v___x_3676_;
}
else
{
lean_object* v_quotContext_3677_; lean_object* v_currMacroScope_3678_; lean_object* v_ref_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v_xs_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_quotContext_3677_ = lean_ctor_get(v_a_3662_, 1);
v_currMacroScope_3678_ = lean_ctor_get(v_a_3662_, 2);
v_ref_3679_ = lean_ctor_get(v_a_3662_, 5);
v___x_3680_ = l_Lean_Syntax_getArg(v___x_3670_, v___x_3668_);
v___x_3681_ = l_Lean_Syntax_getArgs(v___x_3670_);
lean_dec(v___x_3670_);
v___x_3682_ = l_Array_extract___redArg(v___x_3681_, v___x_3669_, v___x_3673_);
lean_dec_ref(v___x_3681_);
v___x_3683_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3684_ = lean_box(2);
v___x_3685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
lean_ctor_set(v___x_3685_, 1, v___x_3683_);
lean_ctor_set(v___x_3685_, 2, v___x_3682_);
v_xs_3686_ = l_Lean_Syntax_getArgs(v___x_3685_);
lean_dec_ref_known(v___x_3685_, 3);
v___x_3687_ = l_Lean_SourceInfo_fromRef(v_ref_3679_, v___x_3672_);
v___x_3688_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3689_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3690_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3687_, 11);
v___x_3691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3687_);
lean_ctor_set(v___x_3691_, 1, v___x_3689_);
v___x_3692_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3693_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3694_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3678_);
lean_inc(v_quotContext_3677_);
v___x_3695_ = l_Lean_addMacroScope(v_quotContext_3677_, v___x_3694_, v_currMacroScope_3678_);
v___x_3696_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3697_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3687_);
lean_ctor_set(v___x_3697_, 1, v___x_3693_);
lean_ctor_set(v___x_3697_, 2, v___x_3695_);
lean_ctor_set(v___x_3697_, 3, v___x_3696_);
v___x_3698_ = l_Lean_Syntax_node2(v___x_3687_, v___x_3690_, v___x_3691_, v___x_3697_);
v___x_3699_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3687_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3702_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3687_);
lean_ctor_set(v___x_3703_, 1, v___x_3701_);
v___x_3704_ = l_Lean_Syntax_node1(v___x_3687_, v___x_3683_, v___x_3680_);
v___x_3705_ = l_Lean_Syntax_node2(v___x_3687_, v___x_3702_, v___x_3703_, v___x_3704_);
v___x_3706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3687_);
lean_ctor_set(v___x_3706_, 1, v___x_3692_);
v___x_3707_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3708_ = l_Array_append___redArg(v___x_3707_, v_xs_3686_);
lean_dec_ref(v_xs_3686_);
v___x_3709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3687_);
lean_ctor_set(v___x_3709_, 1, v___x_3683_);
lean_ctor_set(v___x_3709_, 2, v___x_3708_);
v___x_3710_ = l_Lean_Syntax_node2(v___x_3687_, v___x_3664_, v___x_3706_, v___x_3709_);
lean_inc_ref(v___x_3700_);
v___x_3711_ = l_Lean_Syntax_node5(v___x_3687_, v___x_3683_, v___x_3698_, v___x_3700_, v___x_3705_, v___x_3700_, v___x_3710_);
v___x_3712_ = l_Lean_Syntax_node1(v___x_3687_, v___x_3688_, v___x_3711_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_a_3663_);
return v___x_3713_;
}
}
else
{
lean_object* v_quotContext_3714_; lean_object* v_currMacroScope_3715_; lean_object* v_ref_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v_quotContext_3714_ = lean_ctor_get(v_a_3662_, 1);
v_currMacroScope_3715_ = lean_ctor_get(v_a_3662_, 2);
v_ref_3716_ = lean_ctor_get(v_a_3662_, 5);
v___x_3717_ = l_Lean_Syntax_getArg(v___x_3670_, v___x_3668_);
lean_dec(v___x_3670_);
v___x_3718_ = l_Lean_SourceInfo_fromRef(v_ref_3716_, v___x_3671_);
v___x_3719_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3720_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3721_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3722_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3718_, 8);
v___x_3723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3718_);
lean_ctor_set(v___x_3723_, 1, v___x_3721_);
v___x_3724_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3725_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3715_);
lean_inc(v_quotContext_3714_);
v___x_3726_ = l_Lean_addMacroScope(v_quotContext_3714_, v___x_3725_, v_currMacroScope_3715_);
v___x_3727_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3718_);
lean_ctor_set(v___x_3728_, 1, v___x_3724_);
lean_ctor_set(v___x_3728_, 2, v___x_3726_);
lean_ctor_set(v___x_3728_, 3, v___x_3727_);
v___x_3729_ = l_Lean_Syntax_node2(v___x_3718_, v___x_3722_, v___x_3723_, v___x_3728_);
v___x_3730_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3718_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3733_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3718_);
lean_ctor_set(v___x_3734_, 1, v___x_3732_);
v___x_3735_ = l_Lean_Syntax_node1(v___x_3718_, v___x_3720_, v___x_3717_);
v___x_3736_ = l_Lean_Syntax_node2(v___x_3718_, v___x_3733_, v___x_3734_, v___x_3735_);
v___x_3737_ = l_Lean_Syntax_node3(v___x_3718_, v___x_3720_, v___x_3729_, v___x_3731_, v___x_3736_);
v___x_3738_ = l_Lean_Syntax_node1(v___x_3718_, v___x_3719_, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v_a_3663_);
return v___x_3739_;
}
}
else
{
lean_object* v_quotContext_3740_; lean_object* v_currMacroScope_3741_; lean_object* v_ref_3742_; uint8_t v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_dec(v___x_3670_);
v_quotContext_3740_ = lean_ctor_get(v_a_3662_, 1);
v_currMacroScope_3741_ = lean_ctor_get(v_a_3662_, 2);
v_ref_3742_ = lean_ctor_get(v_a_3662_, 5);
v___x_3743_ = 0;
v___x_3744_ = l_Lean_SourceInfo_fromRef(v_ref_3742_, v___x_3743_);
v___x_3745_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12));
v___x_3746_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13));
lean_inc_n(v___x_3744_, 17);
v___x_3747_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3744_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_3749_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_3750_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3751_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_3752_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_3753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3744_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3755_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
v___x_3756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3744_);
lean_ctor_set(v___x_3756_, 1, v___x_3754_);
v___x_3757_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3758_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3741_);
lean_inc(v_quotContext_3740_);
v___x_3759_ = l_Lean_addMacroScope(v_quotContext_3740_, v___x_3758_, v_currMacroScope_3741_);
v___x_3760_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3761_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3744_);
lean_ctor_set(v___x_3761_, 1, v___x_3757_);
lean_ctor_set(v___x_3761_, 2, v___x_3759_);
lean_ctor_set(v___x_3761_, 3, v___x_3760_);
v___x_3762_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3755_, v___x_3756_, v___x_3761_);
v___x_3763_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3744_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3766_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3767_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3744_);
lean_ctor_set(v___x_3767_, 1, v___x_3765_);
v___x_3768_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3769_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3769_, 0, v___x_3744_);
lean_ctor_set(v___x_3769_, 1, v___x_3750_);
lean_ctor_set(v___x_3769_, 2, v___x_3768_);
v___x_3770_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3766_, v___x_3767_, v___x_3769_);
v___x_3771_ = l_Lean_Syntax_node3(v___x_3744_, v___x_3750_, v___x_3762_, v___x_3764_, v___x_3770_);
v___x_3772_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3749_, v___x_3771_);
v___x_3773_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3748_, v___x_3772_);
v___x_3774_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_3775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3744_);
lean_ctor_set(v___x_3775_, 1, v___x_3774_);
v___x_3776_ = l_Lean_Syntax_node3(v___x_3744_, v___x_3751_, v___x_3753_, v___x_3773_, v___x_3775_);
v___x_3777_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3750_, v___x_3776_);
v___x_3778_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3749_, v___x_3777_);
v___x_3779_ = l_Lean_Syntax_node1(v___x_3744_, v___x_3748_, v___x_3778_);
v___x_3780_ = l_Lean_Syntax_node2(v___x_3744_, v___x_3745_, v___x_3747_, v___x_3779_);
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3780_);
lean_ctor_set(v___x_3781_, 1, v_a_3663_);
return v___x_3781_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___boxed(lean_object* v_x_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
lean_object* v_res_3785_; 
v_res_3785_ = l___aux__Init__NotationExtra______macroRules__tacticFunext________1(v_x_3782_, v_a_3783_, v_a_3784_);
lean_dec_ref(v_a_3783_);
return v_res_3785_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(size_t v_sz_3786_, size_t v_i_3787_, lean_object* v_bs_3788_){
_start:
{
uint8_t v___x_3789_; 
v___x_3789_ = lean_usize_dec_lt(v_i_3787_, v_sz_3786_);
if (v___x_3789_ == 0)
{
return v_bs_3788_;
}
else
{
lean_object* v_v_3790_; lean_object* v___x_3791_; lean_object* v_bs_x27_3792_; size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v_v_3790_ = lean_array_uget(v_bs_3788_, v_i_3787_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v_bs_x27_3792_ = lean_array_uset(v_bs_3788_, v_i_3787_, v___x_3791_);
v___x_3793_ = ((size_t)1ULL);
v___x_3794_ = lean_usize_add(v_i_3787_, v___x_3793_);
v___x_3795_ = lean_array_uset(v_bs_x27_3792_, v_i_3787_, v_v_3790_);
v_i_3787_ = v___x_3794_;
v_bs_3788_ = v___x_3795_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3786_ = stack[0].m_num;
size_t v_i_3787_ = stack[1].m_num;
lean_object* v_bs_3788_ = stack[2].m_obj;
lean_object* v_res_3797_;
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_3786_, v_i_3787_, v_bs_3788_);
stack->m_obj
 = v_res_3797_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1___boxed(lean_object* v_sz_3798_, lean_object* v_i_3799_, lean_object* v_bs_3800_){
_start:
{
size_t v_sz_boxed_3801_; size_t v_i_boxed_3802_; lean_object* v_res_3803_; 
v_sz_boxed_3801_ = lean_unbox_usize(v_sz_3798_);
lean_dec(v_sz_3798_);
v_i_boxed_3802_ = lean_unbox_usize(v_i_3799_);
lean_dec(v_i_3799_);
v_res_3803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_boxed_3801_, v_i_boxed_3802_, v_bs_3800_);
return v_res_3803_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(size_t v_sz_3804_, size_t v_i_3805_, lean_object* v_bs_3806_){
_start:
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_lt(v_i_3805_, v_sz_3804_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_bs_3806_);
return v___x_3808_;
}
else
{
lean_object* v_v_3809_; lean_object* v___x_3810_; lean_object* v_bs_x27_3811_; size_t v___x_3812_; size_t v___x_3813_; lean_object* v___x_3814_; 
v_v_3809_ = lean_array_uget(v_bs_3806_, v_i_3805_);
v___x_3810_ = lean_unsigned_to_nat(0u);
v_bs_x27_3811_ = lean_array_uset(v_bs_3806_, v_i_3805_, v___x_3810_);
v___x_3812_ = ((size_t)1ULL);
v___x_3813_ = lean_usize_add(v_i_3805_, v___x_3812_);
v___x_3814_ = lean_array_uset(v_bs_x27_3811_, v_i_3805_, v_v_3809_);
v_i_3805_ = v___x_3813_;
v_bs_3806_ = v___x_3814_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_3804_ = stack[0].m_num;
size_t v_i_3805_ = stack[1].m_num;
lean_object* v_bs_3806_ = stack[2].m_obj;
lean_object* v_res_3816_;
v_res_3816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_3804_, v_i_3805_, v_bs_3806_);
stack->m_obj
 = v_res_3816_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0___boxed(lean_object* v_sz_3817_, lean_object* v_i_3818_, lean_object* v_bs_3819_){
_start:
{
size_t v_sz_boxed_3820_; size_t v_i_boxed_3821_; lean_object* v_res_3822_; 
v_sz_boxed_3820_ = lean_unbox_usize(v_sz_3817_);
lean_dec(v_sz_3817_);
v_i_boxed_3821_ = lean_unbox_usize(v_i_3818_);
lean_dec(v_i_3818_);
v_res_3822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_boxed_3820_, v_i_boxed_3821_, v_bs_3819_);
return v_res_3822_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(uint8_t v___x_3823_, lean_object* v_as_3824_, size_t v_i_3825_, size_t v_stop_3826_, lean_object* v_b_3827_){
_start:
{
lean_object* v___y_3829_; uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_eq(v_i_3825_, v_stop_3826_);
if (v___x_3833_ == 0)
{
lean_object* v_fst_3834_; uint8_t v___x_3835_; 
v_fst_3834_ = lean_ctor_get(v_b_3827_, 0);
v___x_3835_ = lean_unbox(v_fst_3834_);
if (v___x_3835_ == 0)
{
lean_object* v_snd_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3844_; 
v_snd_3836_ = lean_ctor_get(v_b_3827_, 1);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_b_3827_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v_b_3827_, 0);
lean_dec(v_unused_3845_);
v___x_3838_ = v_b_3827_;
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_snd_3836_);
lean_dec(v_b_3827_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3844_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3840_; lean_object* v___x_3842_; 
v___x_3840_ = lean_box(v___x_3823_);
if (v_isShared_3839_ == 0)
{
lean_ctor_set(v___x_3838_, 0, v___x_3840_);
v___x_3842_ = v___x_3838_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3840_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v_snd_3836_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
v___y_3829_ = v___x_3842_;
goto v___jp_3828_;
}
}
}
else
{
lean_object* v_snd_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3856_; 
v_snd_3846_ = lean_ctor_get(v_b_3827_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_b_3827_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; 
v_unused_3857_ = lean_ctor_get(v_b_3827_, 0);
lean_dec(v_unused_3857_);
v___x_3848_ = v_b_3827_;
v_isShared_3849_ = v_isSharedCheck_3856_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_snd_3846_);
lean_dec(v_b_3827_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3856_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3854_; 
v___x_3850_ = lean_array_uget_borrowed(v_as_3824_, v_i_3825_);
lean_inc(v___x_3850_);
v___x_3851_ = lean_array_push(v_snd_3846_, v___x_3850_);
v___x_3852_ = lean_box(v___x_3833_);
if (v_isShared_3849_ == 0)
{
lean_ctor_set(v___x_3848_, 1, v___x_3851_);
lean_ctor_set(v___x_3848_, 0, v___x_3852_);
v___x_3854_ = v___x_3848_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3852_);
lean_ctor_set(v_reuseFailAlloc_3855_, 1, v___x_3851_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
v___y_3829_ = v___x_3854_;
goto v___jp_3828_;
}
}
}
}
else
{
return v_b_3827_;
}
v___jp_3828_:
{
size_t v___x_3830_; size_t v___x_3831_; 
v___x_3830_ = ((size_t)1ULL);
v___x_3831_ = lean_usize_add(v_i_3825_, v___x_3830_);
v_i_3825_ = v___x_3831_;
v_b_3827_ = v___y_3829_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3823_ = stack[0].m_num;
lean_object* v_as_3824_ = stack[1].m_obj;
size_t v_i_3825_ = stack[2].m_num;
size_t v_stop_3826_ = stack[3].m_num;
lean_object* v_b_3827_ = stack[4].m_obj;
lean_object* v_res_3858_;
v_res_3858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_3823_, v_as_3824_, v_i_3825_, v_stop_3826_, v_b_3827_);
stack->m_obj
 = v_res_3858_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3___boxed(lean_object* v___x_3859_, lean_object* v_as_3860_, lean_object* v_i_3861_, lean_object* v_stop_3862_, lean_object* v_b_3863_){
_start:
{
uint8_t v___x_5046__boxed_3864_; size_t v_i_boxed_3865_; size_t v_stop_boxed_3866_; lean_object* v_res_3867_; 
v___x_5046__boxed_3864_ = lean_unbox(v___x_3859_);
v_i_boxed_3865_ = lean_unbox_usize(v_i_3861_);
lean_dec(v_i_3861_);
v_stop_boxed_3866_ = lean_unbox_usize(v_stop_3862_);
lean_dec(v_stop_3862_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_5046__boxed_3864_, v_as_3860_, v_i_boxed_3865_, v_stop_boxed_3866_, v_b_3863_);
lean_dec_ref(v_as_3860_);
return v_res_3867_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0));
v___x_3870_ = l_String_toRawSubstring_x27(v___x_3869_);
return v___x_3870_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(lean_object* v_as_3887_, size_t v_i_3888_, size_t v_stop_3889_, lean_object* v_b_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v___x_3893_; 
v___x_3893_ = lean_usize_dec_eq(v_i_3888_, v_stop_3889_);
if (v___x_3893_ == 0)
{
lean_object* v_quotContext_3894_; lean_object* v_currMacroScope_3895_; lean_object* v_ref_3896_; size_t v___x_3897_; size_t v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v_quotContext_3894_ = lean_ctor_get(v___y_3891_, 1);
v_currMacroScope_3895_ = lean_ctor_get(v___y_3891_, 2);
v_ref_3896_ = lean_ctor_get(v___y_3891_, 5);
v___x_3897_ = ((size_t)1ULL);
v___x_3898_ = lean_usize_sub(v_i_3888_, v___x_3897_);
v___x_3899_ = lean_array_uget_borrowed(v_as_3887_, v___x_3898_);
v___x_3900_ = l_Lean_SourceInfo_fromRef(v_ref_3896_, v___x_3893_);
v___x_3901_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_3902_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1);
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4));
lean_inc(v_currMacroScope_3895_);
lean_inc(v_quotContext_3894_);
v___x_3904_ = l_Lean_addMacroScope(v_quotContext_3894_, v___x_3903_, v_currMacroScope_3895_);
v___x_3905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8));
lean_inc_n(v___x_3900_, 2);
v___x_3906_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3900_);
lean_ctor_set(v___x_3906_, 1, v___x_3902_);
lean_ctor_set(v___x_3906_, 2, v___x_3904_);
lean_ctor_set(v___x_3906_, 3, v___x_3905_);
v___x_3907_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3899_);
v___x_3908_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3907_, v___x_3899_, v_b_3890_);
v___x_3909_ = l_Lean_Syntax_node2(v___x_3900_, v___x_3901_, v___x_3906_, v___x_3908_);
v_i_3888_ = v___x_3898_;
v_b_3890_ = v___x_3909_;
goto _start;
}
else
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v_b_3890_);
lean_ctor_set(v___x_3911_, 1, v___y_3892_);
return v___x_3911_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3887_ = stack[0].m_obj;
size_t v_i_3888_ = stack[1].m_num;
size_t v_stop_3889_ = stack[2].m_num;
lean_object* v_b_3890_ = stack[3].m_obj;
lean_object* v___y_3891_ = stack[4].m_obj;
lean_object* v___y_3892_ = stack[5].m_obj;
lean_object* v_res_3912_;
v_res_3912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_as_3887_, v_i_3888_, v_stop_3889_, v_b_3890_, v___y_3891_, v___y_3892_);
stack->m_obj
 = v_res_3912_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___boxed(lean_object* v_as_3913_, lean_object* v_i_3914_, lean_object* v_stop_3915_, lean_object* v_b_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
size_t v_i_boxed_3919_; size_t v_stop_boxed_3920_; lean_object* v_res_3921_; 
v_i_boxed_3919_ = lean_unbox_usize(v_i_3914_);
lean_dec(v_i_3914_);
v_stop_boxed_3920_ = lean_unbox_usize(v_stop_3915_);
lean_dec(v_stop_3915_);
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_as_3913_, v_i_boxed_3919_, v_stop_boxed_3920_, v_b_3916_, v___y_3917_, v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_as_3913_);
return v_res_3921_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13(void){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12));
v___x_3957_ = l_String_toRawSubstring_x27(v___x_3956_);
return v___x_3957_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16(void){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3962_ = l_Lean_mkAtom(v___x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(lean_object* v_x_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3966_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1));
lean_inc(v_x_3963_);
v___x_3967_ = l_Lean_Syntax_isOfKind(v_x_3963_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec(v_x_3963_);
v___x_3968_ = lean_box(1);
v___x_3969_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v_a_3965_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; lean_object* v___y_3972_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; uint8_t v___x_4061_; 
v___x_3970_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_unsigned_to_nat(1u);
v___x_4057_ = l_Lean_Syntax_getArg(v_x_3963_, v___x_4056_);
v___x_4058_ = l_Lean_Syntax_getArgs(v___x_4057_);
lean_dec(v___x_4057_);
v___x_4059_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___x_4060_ = lean_array_get_size(v___x_4058_);
v___x_4061_ = lean_nat_dec_lt(v___x_3970_, v___x_4060_);
if (v___x_4061_ == 0)
{
lean_dec_ref(v___x_4058_);
v___y_3972_ = v___x_4059_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_4062_; lean_object* v___x_4063_; size_t v___x_4064_; size_t v___x_4065_; lean_object* v___x_4066_; lean_object* v_snd_4067_; 
v___x_4062_ = lean_box(v___x_4061_);
v___x_4063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
lean_ctor_set(v___x_4063_, 1, v___x_4059_);
v___x_4064_ = ((size_t)0ULL);
v___x_4065_ = lean_usize_of_nat(v___x_4060_);
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_3967_, v___x_4058_, v___x_4064_, v___x_4065_, v___x_4063_);
lean_dec_ref(v___x_4058_);
v_snd_4067_ = lean_ctor_get(v___x_4066_, 1);
lean_inc(v_snd_4067_);
lean_dec_ref(v___x_4066_);
v___y_3972_ = v_snd_4067_;
goto v___jp_3971_;
}
v___jp_3971_:
{
size_t v_sz_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v_sz_3973_ = lean_array_size(v___y_3972_);
v___x_3974_ = ((size_t)0ULL);
v___x_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_3973_, v___x_3974_, v___y_3972_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
lean_dec(v_x_3963_);
v___x_3976_ = lean_box(1);
v___x_3977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
lean_ctor_set(v___x_3977_, 1, v_a_3965_);
return v___x_3977_;
}
else
{
lean_object* v_val_3978_; lean_object* v___x_3979_; lean_object* v_k_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v_val_3978_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v___x_3975_, 1);
v___x_3979_ = lean_unsigned_to_nat(3u);
v_k_3980_ = l_Lean_Syntax_getArg(v_x_3963_, v___x_3979_);
lean_dec(v_x_3963_);
v___x_3981_ = lean_array_get_size(v_val_3978_);
v___x_3982_ = lean_unsigned_to_nat(8u);
v___x_3983_ = lean_nat_dec_lt(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; lean_object* v_m_3985_; lean_object* v_quotContext_3986_; lean_object* v_currMacroScope_3987_; lean_object* v_ref_3988_; lean_object* v_y_3989_; lean_object* v_z_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; size_t v_sz_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; size_t v_sz_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_3984_ = lean_unsigned_to_nat(1u);
v_m_3985_ = lean_nat_shiftr(v___x_3981_, v___x_3984_);
v_quotContext_3986_ = lean_ctor_get(v_a_3964_, 1);
v_currMacroScope_3987_ = lean_ctor_get(v_a_3964_, 2);
v_ref_3988_ = lean_ctor_get(v_a_3964_, 5);
lean_inc(v_m_3985_);
v_y_3989_ = l_Array_extract___redArg(v_val_3978_, v_m_3985_, v___x_3981_);
v_z_3990_ = l_Array_extract___redArg(v_val_3978_, v___x_3970_, v_m_3985_);
lean_dec(v_val_3978_);
v___x_3991_ = l_Lean_SourceInfo_fromRef(v_ref_3988_, v___x_3983_);
v___x_3992_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2));
v___x_3993_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3));
lean_inc_n(v___x_3991_, 15);
v___x_3994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3991_);
lean_ctor_set(v___x_3994_, 1, v___x_3992_);
v___x_3995_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5));
v___x_3996_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3997_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3991_);
lean_ctor_set(v___x_3998_, 1, v___x_3996_);
lean_ctor_set(v___x_3998_, 2, v___x_3997_);
lean_inc_ref_n(v___x_3998_, 3);
v___x_3999_ = l_Lean_Syntax_node1(v___x_3991_, v___x_3995_, v___x_3998_);
v___x_4000_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7));
v___x_4001_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9));
v___x_4002_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11));
v___x_4003_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13);
v___x_4004_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14));
lean_inc(v_currMacroScope_3987_);
lean_inc(v_quotContext_3986_);
v___x_4005_ = l_Lean_addMacroScope(v_quotContext_3986_, v___x_4004_, v_currMacroScope_3987_);
v___x_4006_ = lean_box(0);
v___x_4007_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4007_, 0, v___x_3991_);
lean_ctor_set(v___x_4007_, 1, v___x_4003_);
lean_ctor_set(v___x_4007_, 2, v___x_4005_);
lean_ctor_set(v___x_4007_, 3, v___x_4006_);
lean_inc_ref(v___x_4007_);
v___x_4008_ = l_Lean_Syntax_node1(v___x_3991_, v___x_4002_, v___x_4007_);
v___x_4009_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_4010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_3991_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___x_4011_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15));
v___x_4012_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4012_, 0, v___x_3991_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v_sz_4013_ = lean_array_size(v_y_3989_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_4013_, v___x_3974_, v_y_3989_);
v___x_4015_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_4016_ = l_Lean_mkSepArray(v___x_4014_, v___x_4015_);
lean_dec_ref(v___x_4014_);
v___x_4017_ = l_Array_append___redArg(v___x_3997_, v___x_4016_);
lean_dec_ref(v___x_4016_);
v___x_4018_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4018_, 0, v___x_3991_);
lean_ctor_set(v___x_4018_, 1, v___x_3996_);
lean_ctor_set(v___x_4018_, 2, v___x_4017_);
v___x_4019_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_3991_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
v___x_4021_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_4022_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4022_, 0, v___x_3991_);
lean_ctor_set(v___x_4022_, 1, v___x_4021_);
lean_inc_ref(v___x_4022_);
lean_inc_ref(v___x_4020_);
lean_inc_ref(v___x_4012_);
v___x_4023_ = l_Lean_Syntax_node5(v___x_3991_, v___x_3966_, v___x_4012_, v___x_4018_, v___x_4020_, v_k_3980_, v___x_4022_);
v___x_4024_ = l_Lean_Syntax_node5(v___x_3991_, v___x_4001_, v___x_4008_, v___x_3998_, v___x_3998_, v___x_4010_, v___x_4023_);
v___x_4025_ = l_Lean_Syntax_node1(v___x_3991_, v___x_4000_, v___x_4024_);
v_sz_4026_ = lean_array_size(v_z_3990_);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_4026_, v___x_3974_, v_z_3990_);
v___x_4028_ = l_Lean_mkSepArray(v___x_4027_, v___x_4015_);
lean_dec_ref(v___x_4027_);
v___x_4029_ = l_Array_append___redArg(v___x_3997_, v___x_4028_);
lean_dec_ref(v___x_4028_);
v___x_4030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4030_, 0, v___x_3991_);
lean_ctor_set(v___x_4030_, 1, v___x_3996_);
lean_ctor_set(v___x_4030_, 2, v___x_4029_);
v___x_4031_ = l_Lean_Syntax_node5(v___x_3991_, v___x_3966_, v___x_4012_, v___x_4030_, v___x_4020_, v___x_4007_, v___x_4022_);
v___x_4032_ = l_Lean_Syntax_node5(v___x_3991_, v___x_3993_, v___x_3994_, v___x_3999_, v___x_4025_, v___x_3998_, v___x_4031_);
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v_a_3965_);
return v___x_4033_;
}
else
{
uint8_t v___x_4034_; 
v___x_4034_ = lean_nat_dec_lt(v___x_3970_, v___x_3981_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; 
lean_dec(v_val_3978_);
v___x_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4035_, 0, v_k_3980_);
lean_ctor_set(v___x_4035_, 1, v_a_3965_);
return v___x_4035_;
}
else
{
size_t v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_usize_of_nat(v___x_3981_);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_val_3978_, v___x_4036_, v___x_3974_, v_k_3980_, v_a_3964_, v_a_3965_);
lean_dec(v_val_3978_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_a_4039_ = lean_ctor_get(v___x_4037_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4037_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
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
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_4047_; lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
v_a_4047_ = lean_ctor_get(v___x_4037_, 0);
v_a_4048_ = lean_ctor_get(v___x_4037_, 1);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4037_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_inc(v_a_4047_);
lean_dec(v___x_4037_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4047_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
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
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___boxed(lean_object* v_x_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(v_x_4068_, v_a_4069_, v_a_4070_);
lean_dec_ref(v_a_4069_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(lean_object* v_x_4160_){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4161_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1));
v___x_4162_ = l_Lean_Name_append(v_x_4160_, v___x_4161_);
return v___x_4162_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(lean_object* v___x_4169_, size_t v_sz_4170_, size_t v_i_4171_, lean_object* v_bs_4172_){
_start:
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_usize_dec_lt(v_i_4171_, v_sz_4170_);
if (v___x_4173_ == 0)
{
lean_dec(v___x_4169_);
return v_bs_4172_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v_v_4176_; lean_object* v___x_4177_; lean_object* v_bs_x27_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; size_t v___x_4182_; size_t v___x_4183_; lean_object* v___x_4184_; 
v___x_4174_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4175_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_v_4176_ = lean_array_uget(v_bs_4172_, v_i_4171_);
v___x_4177_ = lean_unsigned_to_nat(0u);
v_bs_x27_4178_ = lean_array_uset(v_bs_4172_, v_i_4171_, v___x_4177_);
v___x_4179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1));
lean_inc_n(v___x_4169_, 2);
v___x_4180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4169_);
lean_ctor_set(v___x_4180_, 1, v___x_4174_);
lean_ctor_set(v___x_4180_, 2, v___x_4175_);
v___x_4181_ = l_Lean_Syntax_node2(v___x_4169_, v___x_4179_, v___x_4180_, v_v_4176_);
v___x_4182_ = ((size_t)1ULL);
v___x_4183_ = lean_usize_add(v_i_4171_, v___x_4182_);
v___x_4184_ = lean_array_uset(v_bs_x27_4178_, v_i_4171_, v___x_4181_);
v_i_4171_ = v___x_4183_;
v_bs_4172_ = v___x_4184_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4169_ = stack[0].m_obj;
size_t v_sz_4170_ = stack[1].m_num;
size_t v_i_4171_ = stack[2].m_num;
lean_object* v_bs_4172_ = stack[3].m_obj;
lean_object* v_res_4186_;
v_res_4186_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___x_4169_, v_sz_4170_, v_i_4171_, v_bs_4172_);
stack->m_obj
 = v_res_4186_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___boxed(lean_object* v___x_4187_, lean_object* v_sz_4188_, lean_object* v_i_4189_, lean_object* v_bs_4190_){
_start:
{
size_t v_sz_boxed_4191_; size_t v_i_boxed_4192_; lean_object* v_res_4193_; 
v_sz_boxed_4191_ = lean_unbox_usize(v_sz_4188_);
lean_dec(v_sz_4188_);
v_i_boxed_4192_ = lean_unbox_usize(v_i_4189_);
lean_dec(v_i_4189_);
v_res_4193_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___x_4187_, v_sz_boxed_4191_, v_i_boxed_4192_, v_bs_4190_);
return v_res_4193_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(size_t v_sz_4194_, size_t v_i_4195_, lean_object* v_bs_4196_){
_start:
{
uint8_t v___x_4197_; 
v___x_4197_ = lean_usize_dec_lt(v_i_4195_, v_sz_4194_);
if (v___x_4197_ == 0)
{
lean_object* v___x_4198_; 
v___x_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4198_, 0, v_bs_4196_);
return v___x_4198_;
}
else
{
lean_object* v_v_4199_; lean_object* v___x_4200_; uint8_t v___x_4201_; 
v_v_4199_ = lean_array_uget(v_bs_4196_, v_i_4195_);
v___x_4200_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4199_);
v___x_4201_ = l_Lean_Syntax_isOfKind(v_v_4199_, v___x_4200_);
if (v___x_4201_ == 0)
{
lean_object* v___x_4202_; 
lean_dec(v_v_4199_);
lean_dec_ref(v_bs_4196_);
v___x_4202_ = lean_box(0);
return v___x_4202_;
}
else
{
lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v_bs_x27_4205_; lean_object* v_parents_4206_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_unsigned_to_nat(1u);
v_bs_x27_4205_ = lean_array_uset(v_bs_4196_, v_i_4195_, v___x_4203_);
v_parents_4206_ = l_Lean_Syntax_getArg(v_v_4199_, v___x_4203_);
v___x_4212_ = l_Lean_Syntax_getArg(v_v_4199_, v___x_4204_);
lean_dec(v_v_4199_);
v___x_4213_ = l_Lean_Syntax_isNone(v___x_4212_);
if (v___x_4213_ == 0)
{
uint8_t v___x_4214_; 
v___x_4214_ = l_Lean_Syntax_matchesNull(v___x_4212_, v___x_4204_);
if (v___x_4214_ == 0)
{
lean_object* v___x_4215_; 
lean_dec(v_parents_4206_);
lean_dec_ref(v_bs_x27_4205_);
v___x_4215_ = lean_box(0);
return v___x_4215_;
}
else
{
goto v___jp_4207_;
}
}
else
{
lean_dec(v___x_4212_);
goto v___jp_4207_;
}
v___jp_4207_:
{
size_t v___x_4208_; size_t v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = ((size_t)1ULL);
v___x_4209_ = lean_usize_add(v_i_4195_, v___x_4208_);
v___x_4210_ = lean_array_uset(v_bs_x27_4205_, v_i_4195_, v_parents_4206_);
v_i_4195_ = v___x_4209_;
v_bs_4196_ = v___x_4210_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4194_ = stack[0].m_num;
size_t v_i_4195_ = stack[1].m_num;
lean_object* v_bs_4196_ = stack[2].m_obj;
lean_object* v_res_4216_;
v_res_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_4194_, v_i_4195_, v_bs_4196_);
stack->m_obj
 = v_res_4216_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0___boxed(lean_object* v_sz_4217_, lean_object* v_i_4218_, lean_object* v_bs_4219_){
_start:
{
size_t v_sz_boxed_4220_; size_t v_i_boxed_4221_; lean_object* v_res_4222_; 
v_sz_boxed_4220_ = lean_unbox_usize(v_sz_4217_);
lean_dec(v_sz_4217_);
v_i_boxed_4221_ = lean_unbox_usize(v_i_4218_);
lean_dec(v_i_4218_);
v_res_4222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_boxed_4220_, v_i_boxed_4221_, v_bs_4219_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(lean_object* v_x_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; 
v___x_4278_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_4279_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_4280_ = ((lean_object*)(l_Lean_Parser_Command_classAbbrev___closed__1));
lean_inc(v_x_4275_);
v___x_4281_ = l_Lean_Syntax_isOfKind(v_x_4275_, v___x_4280_);
if (v___x_4281_ == 0)
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
lean_dec(v_x_4275_);
v___x_4282_ = lean_box(1);
v___x_4283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4282_);
lean_ctor_set(v___x_4283_, 1, v_a_4277_);
return v___x_4283_;
}
else
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; 
v___x_4284_ = lean_unsigned_to_nat(0u);
v___x_4285_ = l_Lean_Syntax_getArg(v_x_4275_, v___x_4284_);
v___x_4286_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0));
lean_inc(v___x_4285_);
v___x_4287_ = l_Lean_Syntax_isOfKind(v___x_4285_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; 
lean_dec(v___x_4285_);
lean_dec(v_x_4275_);
v___x_4288_ = lean_box(1);
v___x_4289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4288_);
lean_ctor_set(v___x_4289_, 1, v_a_4277_);
return v___x_4289_;
}
else
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; size_t v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; size_t v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4354_; lean_object* v___y_4355_; lean_object* v___y_4356_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v_ty_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4290_ = lean_unsigned_to_nat(3u);
v___x_4291_ = l_Lean_Syntax_getArg(v_x_4275_, v___x_4290_);
v___x_4384_ = lean_unsigned_to_nat(4u);
v___x_4385_ = l_Lean_Syntax_getArg(v_x_4275_, v___x_4384_);
v___x_4419_ = lean_unsigned_to_nat(5u);
v___x_4420_ = l_Lean_Syntax_getArg(v_x_4275_, v___x_4419_);
v___x_4421_ = l_Lean_Syntax_isNone(v___x_4420_);
if (v___x_4421_ == 0)
{
lean_object* v___x_4422_; uint8_t v___x_4423_; 
v___x_4422_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4420_);
v___x_4423_ = l_Lean_Syntax_matchesNull(v___x_4420_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_dec(v___x_4420_);
lean_dec(v___x_4385_);
lean_dec(v___x_4291_);
lean_dec(v___x_4285_);
lean_dec(v_x_4275_);
v___x_4424_ = lean_box(1);
v___x_4425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4424_);
lean_ctor_set(v___x_4425_, 1, v_a_4277_);
return v___x_4425_;
}
else
{
lean_object* v___x_4426_; lean_object* v_ty_4427_; lean_object* v___x_4428_; 
v___x_4426_ = lean_unsigned_to_nat(1u);
v_ty_4427_ = l_Lean_Syntax_getArg(v___x_4420_, v___x_4426_);
lean_dec(v___x_4420_);
v___x_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4428_, 0, v_ty_4427_);
v_ty_4387_ = v___x_4428_;
v___y_4388_ = v_a_4276_;
v___y_4389_ = v_a_4277_;
goto v___jp_4386_;
}
}
else
{
lean_object* v___x_4429_; 
lean_dec(v___x_4420_);
v___x_4429_ = lean_box(0);
v_ty_4387_ = v___x_4429_;
v___y_4388_ = v_a_4276_;
v___y_4389_ = v_a_4277_;
goto v___jp_4386_;
}
v___jp_4292_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; size_t v_sz_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
lean_inc_ref_n(v___y_4294_, 2);
v___x_4307_ = l_Array_append___redArg(v___y_4294_, v___y_4306_);
lean_dec_ref(v___y_4306_);
lean_inc_n(v___y_4302_, 7);
lean_inc_n(v___y_4305_, 21);
v___x_4308_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4308_, 0, v___y_4305_);
lean_ctor_set(v___x_4308_, 1, v___y_4302_);
lean_ctor_set(v___x_4308_, 2, v___x_4307_);
lean_inc(v___y_4301_);
v___x_4309_ = l_Lean_Syntax_node2(v___y_4305_, v___y_4301_, v___y_4293_, v___x_4308_);
v___x_4310_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1));
v___x_4311_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2));
v___x_4312_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___y_4305_);
lean_ctor_set(v___x_4312_, 1, v___x_4310_);
v_sz_4313_ = lean_array_size(v___y_4296_);
v___x_4314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___y_4305_, v_sz_4313_, v___y_4304_, v___y_4296_);
v___x_4315_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_4316_ = l_Lean_mkSepArray(v___x_4314_, v___x_4315_);
lean_dec_ref(v___x_4314_);
v___x_4317_ = l_Array_append___redArg(v___y_4294_, v___x_4316_);
lean_dec_ref(v___x_4316_);
v___x_4318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4318_, 0, v___y_4305_);
lean_ctor_set(v___x_4318_, 1, v___y_4302_);
lean_ctor_set(v___x_4318_, 2, v___x_4317_);
v___x_4319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4319_, 0, v___y_4305_);
lean_ctor_set(v___x_4319_, 1, v___y_4302_);
lean_ctor_set(v___x_4319_, 2, v___y_4294_);
lean_inc_ref_n(v___x_4319_, 4);
v___x_4320_ = l_Lean_Syntax_node3(v___y_4305_, v___x_4311_, v___x_4312_, v___x_4318_, v___x_4319_);
v___x_4321_ = l_Lean_Syntax_node1(v___y_4305_, v___y_4302_, v___x_4320_);
v___x_4322_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4));
v___x_4323_ = l_Lean_Syntax_node1(v___y_4305_, v___x_4322_, v___x_4319_);
lean_inc(v___y_4295_);
v___x_4324_ = l_Lean_Syntax_node6(v___y_4305_, v___y_4295_, v___y_4298_, v___x_4291_, v___x_4309_, v___x_4321_, v___x_4319_, v___x_4323_);
lean_inc(v___y_4297_);
v___x_4325_ = l_Lean_Syntax_node2(v___y_4305_, v___y_4297_, v___x_4285_, v___x_4324_);
v___x_4326_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5));
v___x_4327_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6));
v___x_4328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4328_, 0, v___y_4305_);
lean_ctor_set(v___x_4328_, 1, v___x_4326_);
v___x_4329_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_4330_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4330_, 0, v___y_4305_);
lean_ctor_set(v___x_4330_, 1, v___x_4329_);
v___x_4331_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
lean_inc_ref_n(v___y_4300_, 2);
v___x_4332_ = l_Lean_Name_mkStr4(v___x_4278_, v___x_4279_, v___y_4300_, v___x_4331_);
v___x_4333_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6));
v___x_4334_ = l_Lean_Name_mkStr4(v___x_4278_, v___x_4279_, v___y_4300_, v___x_4333_);
v___x_4335_ = l_Lean_Syntax_node1(v___y_4305_, v___x_4334_, v___x_4319_);
v___x_4336_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7));
v___x_4337_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8));
v___x_4338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___y_4305_);
lean_ctor_set(v___x_4338_, 1, v___x_4336_);
v___x_4339_ = l_Lean_Syntax_node2(v___y_4305_, v___x_4337_, v___x_4338_, v___x_4319_);
v___x_4340_ = l_Lean_Syntax_node2(v___y_4305_, v___x_4332_, v___x_4335_, v___x_4339_);
v___x_4341_ = l_Lean_Syntax_node1(v___y_4305_, v___y_4302_, v___x_4340_);
v___x_4342_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_4343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___y_4305_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = l_Lean_Syntax_node1(v___y_4305_, v___y_4302_, v___y_4299_);
v___x_4345_ = l_Lean_Syntax_node5(v___y_4305_, v___x_4327_, v___x_4328_, v___x_4330_, v___x_4341_, v___x_4343_, v___x_4344_);
v___x_4346_ = l_Lean_Syntax_node2(v___y_4305_, v___y_4302_, v___x_4325_, v___x_4345_);
v___x_4347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v___y_4303_);
return v___x_4347_;
}
v___jp_4348_:
{
lean_object* v_ref_4357_; uint8_t v___x_4358_; lean_object* v_ctor_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; size_t v_sz_4370_; lean_object* v___x_4371_; size_t v_sz_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_ref_4357_ = lean_ctor_get(v___y_4350_, 5);
v___x_4358_ = 0;
v_ctor_4359_ = l_Lean_mkIdentFrom(v___x_4291_, v___y_4356_, v___x_4358_);
v___x_4360_ = l_Lean_SourceInfo_fromRef(v_ref_4357_, v___x_4358_);
v___x_4361_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4362_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9));
v___x_4363_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11));
v___x_4364_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13));
v___x_4365_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14));
lean_inc_n(v___x_4360_, 3);
v___x_4366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4360_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l_Lean_Syntax_node1(v___x_4360_, v___x_4364_, v___x_4366_);
v___x_4368_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15));
v___x_4369_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4370_ = lean_array_size(v___y_4353_);
v___x_4371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_4370_, v___y_4352_, v___y_4353_);
v_sz_4372_ = lean_array_size(v___x_4371_);
v___x_4373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_4372_, v___y_4352_, v___x_4371_);
v___x_4374_ = l_Array_append___redArg(v___x_4369_, v___x_4373_);
lean_dec_ref(v___x_4373_);
v___x_4375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4360_);
lean_ctor_set(v___x_4375_, 1, v___x_4361_);
lean_ctor_set(v___x_4375_, 2, v___x_4374_);
if (lean_obj_tag(v___y_4354_) == 1)
{
lean_object* v_val_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_val_4376_ = lean_ctor_get(v___y_4354_, 0);
lean_inc(v_val_4376_);
lean_dec_ref_known(v___y_4354_, 1);
v___x_4377_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref(v___y_4355_);
v___x_4378_ = l_Lean_Name_mkStr4(v___x_4278_, v___x_4279_, v___y_4355_, v___x_4377_);
v___x_4379_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
lean_inc_n(v___x_4360_, 2);
v___x_4380_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4360_);
lean_ctor_set(v___x_4380_, 1, v___x_4379_);
v___x_4381_ = l_Lean_Syntax_node2(v___x_4360_, v___x_4378_, v___x_4380_, v_val_4376_);
v___x_4382_ = l_Array_mkArray1___redArg(v___x_4381_);
v___y_4293_ = v___x_4375_;
v___y_4294_ = v___x_4369_;
v___y_4295_ = v___x_4363_;
v___y_4296_ = v___y_4351_;
v___y_4297_ = v___x_4362_;
v___y_4298_ = v___x_4367_;
v___y_4299_ = v_ctor_4359_;
v___y_4300_ = v___y_4355_;
v___y_4301_ = v___x_4368_;
v___y_4302_ = v___x_4361_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4352_;
v___y_4305_ = v___x_4360_;
v___y_4306_ = v___x_4382_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4383_; 
lean_dec(v___y_4354_);
v___x_4383_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___y_4293_ = v___x_4375_;
v___y_4294_ = v___x_4369_;
v___y_4295_ = v___x_4363_;
v___y_4296_ = v___y_4351_;
v___y_4297_ = v___x_4362_;
v___y_4298_ = v___x_4367_;
v___y_4299_ = v_ctor_4359_;
v___y_4300_ = v___y_4355_;
v___y_4301_ = v___x_4368_;
v___y_4302_ = v___x_4361_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4352_;
v___y_4305_ = v___x_4360_;
v___y_4306_ = v___x_4383_;
goto v___jp_4292_;
}
}
v___jp_4386_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; size_t v_sz_4393_; size_t v___x_4394_; lean_object* v___x_4395_; 
v___x_4390_ = lean_unsigned_to_nat(7u);
v___x_4391_ = l_Lean_Syntax_getArg(v_x_4275_, v___x_4390_);
lean_dec(v_x_4275_);
v___x_4392_ = l_Lean_Syntax_getArgs(v___x_4391_);
lean_dec(v___x_4391_);
v_sz_4393_ = lean_array_size(v___x_4392_);
v___x_4394_ = ((size_t)0ULL);
v___x_4395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_4393_, v___x_4394_, v___x_4392_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_dec(v_ty_4387_);
lean_dec(v___x_4385_);
lean_dec(v___x_4291_);
lean_dec(v___x_4285_);
v___x_4396_ = lean_box(1);
v___x_4397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___y_4389_);
return v___x_4397_;
}
else
{
lean_object* v_val_4398_; lean_object* v___x_4399_; lean_object* v_params_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; uint8_t v___x_4403_; 
v_val_4398_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_val_4398_);
lean_dec_ref_known(v___x_4395_, 1);
v___x_4399_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v_params_4400_ = l_Lean_Syntax_getArgs(v___x_4385_);
lean_dec(v___x_4385_);
v___x_4401_ = l_Lean_Syntax_getArg(v___x_4291_, v___x_4284_);
v___x_4402_ = l_Lean_Syntax_getId(v___x_4401_);
lean_dec(v___x_4401_);
v___x_4403_ = l_Lean_Name_hasMacroScopes(v___x_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; 
v___x_4404_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v___x_4402_);
v___y_4349_ = v___y_4389_;
v___y_4350_ = v___y_4388_;
v___y_4351_ = v_val_4398_;
v___y_4352_ = v___x_4394_;
v___y_4353_ = v_params_4400_;
v___y_4354_ = v_ty_4387_;
v___y_4355_ = v___x_4399_;
v___y_4356_ = v___x_4404_;
goto v___jp_4348_;
}
else
{
lean_object* v_view_4405_; lean_object* v_name_4406_; lean_object* v_imported_4407_; lean_object* v_ctx_4408_; lean_object* v_scopes_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4418_; 
v_view_4405_ = l_Lean_extractMacroScopes(v___x_4402_);
v_name_4406_ = lean_ctor_get(v_view_4405_, 0);
v_imported_4407_ = lean_ctor_get(v_view_4405_, 1);
v_ctx_4408_ = lean_ctor_get(v_view_4405_, 2);
v_scopes_4409_ = lean_ctor_get(v_view_4405_, 3);
v_isSharedCheck_4418_ = !lean_is_exclusive(v_view_4405_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4411_ = v_view_4405_;
v_isShared_4412_ = v_isSharedCheck_4418_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_scopes_4409_);
lean_inc(v_ctx_4408_);
lean_inc(v_imported_4407_);
lean_inc(v_name_4406_);
lean_dec(v_view_4405_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4418_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4413_; lean_object* v___x_4415_; 
v___x_4413_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v_name_4406_);
if (v_isShared_4412_ == 0)
{
lean_ctor_set(v___x_4411_, 0, v___x_4413_);
v___x_4415_ = v___x_4411_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4413_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_imported_4407_);
lean_ctor_set(v_reuseFailAlloc_4417_, 2, v_ctx_4408_);
lean_ctor_set(v_reuseFailAlloc_4417_, 3, v_scopes_4409_);
v___x_4415_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
lean_object* v___x_4416_; 
v___x_4416_ = l_Lean_MacroScopesView_review(v___x_4415_);
v___y_4349_ = v___y_4389_;
v___y_4350_ = v___y_4388_;
v___y_4351_ = v_val_4398_;
v___y_4352_ = v___x_4394_;
v___y_4353_ = v_params_4400_;
v___y_4354_ = v_ty_4387_;
v___y_4355_ = v___x_4399_;
v___y_4356_ = v___x_4416_;
goto v___jp_4348_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___boxed(lean_object* v_x_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_){
_start:
{
lean_object* v_res_4433_; 
v_res_4433_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(v_x_4430_, v_a_4431_, v_a_4432_);
lean_dec_ref(v_a_4431_);
return v_res_4433_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(size_t v_sz_4518_, size_t v_i_4519_, lean_object* v_bs_4520_){
_start:
{
uint8_t v___x_4521_; 
v___x_4521_ = lean_usize_dec_lt(v_i_4519_, v_sz_4518_);
if (v___x_4521_ == 0)
{
lean_object* v___x_4522_; 
v___x_4522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4522_, 0, v_bs_4520_);
return v___x_4522_;
}
else
{
lean_object* v_v_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; 
v_v_4523_ = lean_array_uget(v_bs_4520_, v_i_4519_);
v___x_4524_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4523_);
v___x_4525_ = l_Lean_Syntax_isOfKind(v_v_4523_, v___x_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; 
lean_dec(v_v_4523_);
lean_dec_ref(v_bs_4520_);
v___x_4526_ = lean_box(0);
return v___x_4526_;
}
else
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v_bs_x27_4529_; lean_object* v_ts_4530_; size_t v___x_4531_; size_t v___x_4532_; lean_object* v___x_4533_; 
v___x_4527_ = lean_unsigned_to_nat(1u);
v___x_4528_ = lean_unsigned_to_nat(0u);
v_bs_x27_4529_ = lean_array_uset(v_bs_4520_, v_i_4519_, v___x_4528_);
v_ts_4530_ = l_Lean_Syntax_getArg(v_v_4523_, v___x_4527_);
lean_dec(v_v_4523_);
v___x_4531_ = ((size_t)1ULL);
v___x_4532_ = lean_usize_add(v_i_4519_, v___x_4531_);
v___x_4533_ = lean_array_uset(v_bs_x27_4529_, v_i_4519_, v_ts_4530_);
v_i_4519_ = v___x_4532_;
v_bs_4520_ = v___x_4533_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4518_ = stack[0].m_num;
size_t v_i_4519_ = stack[1].m_num;
lean_object* v_bs_4520_ = stack[2].m_obj;
lean_object* v_res_4535_;
v_res_4535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_4518_, v_i_4519_, v_bs_4520_);
stack->m_obj
 = v_res_4535_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0___boxed(lean_object* v_sz_4536_, lean_object* v_i_4537_, lean_object* v_bs_4538_){
_start:
{
size_t v_sz_boxed_4539_; size_t v_i_boxed_4540_; lean_object* v_res_4541_; 
v_sz_boxed_4539_ = lean_unbox_usize(v_sz_4536_);
lean_dec(v_sz_4536_);
v_i_boxed_4540_ = lean_unbox_usize(v_i_4537_);
lean_dec(v_i_4537_);
v_res_4541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_boxed_4539_, v_i_boxed_4540_, v_bs_4538_);
return v_res_4541_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(lean_object* v___x_4548_, size_t v_sz_4549_, size_t v_i_4550_, lean_object* v_bs_4551_){
_start:
{
uint8_t v___x_4552_; 
v___x_4552_ = lean_usize_dec_lt(v_i_4550_, v_sz_4549_);
if (v___x_4552_ == 0)
{
lean_dec(v___x_4548_);
return v_bs_4551_;
}
else
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v_v_4556_; lean_object* v___x_4557_; lean_object* v_bs_x27_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; size_t v___x_4578_; size_t v___x_4579_; lean_object* v___x_4580_; 
v___x_4553_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4554_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4555_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v_v_4556_ = lean_array_uget(v_bs_4551_, v_i_4550_);
v___x_4557_ = lean_unsigned_to_nat(0u);
v_bs_x27_4558_ = lean_array_uset(v_bs_4551_, v_i_4550_, v___x_4557_);
v___x_4559_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_4560_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
lean_inc_n(v___x_4548_, 11);
v___x_4561_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4548_);
lean_ctor_set(v___x_4561_, 1, v___x_4560_);
v___x_4562_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_4563_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_4564_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4548_);
lean_ctor_set(v___x_4564_, 1, v___x_4563_);
v___x_4565_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4566_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4566_, 0, v___x_4548_);
lean_ctor_set(v___x_4566_, 1, v___x_4565_);
v___x_4567_ = l_Lean_Syntax_node3(v___x_4548_, v___x_4562_, v___x_4564_, v_v_4556_, v___x_4566_);
v___x_4568_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_4569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4548_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
v___x_4570_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0));
v___x_4571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1));
v___x_4572_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4572_, 0, v___x_4548_);
lean_ctor_set(v___x_4572_, 1, v___x_4570_);
v___x_4573_ = l_Lean_Syntax_node1(v___x_4548_, v___x_4571_, v___x_4572_);
v___x_4574_ = l_Lean_Syntax_node3(v___x_4548_, v___x_4554_, v___x_4567_, v___x_4569_, v___x_4573_);
v___x_4575_ = l_Lean_Syntax_node1(v___x_4548_, v___x_4553_, v___x_4574_);
v___x_4576_ = l_Lean_Syntax_node1(v___x_4548_, v___x_4555_, v___x_4575_);
v___x_4577_ = l_Lean_Syntax_node2(v___x_4548_, v___x_4559_, v___x_4561_, v___x_4576_);
v___x_4578_ = ((size_t)1ULL);
v___x_4579_ = lean_usize_add(v_i_4550_, v___x_4578_);
v___x_4580_ = lean_array_uset(v_bs_x27_4558_, v_i_4550_, v___x_4577_);
v_i_4550_ = v___x_4579_;
v_bs_4551_ = v___x_4580_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4548_ = stack[0].m_obj;
size_t v_sz_4549_ = stack[1].m_num;
size_t v_i_4550_ = stack[2].m_num;
lean_object* v_bs_4551_ = stack[3].m_obj;
lean_object* v_res_4582_;
v_res_4582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4548_, v_sz_4549_, v_i_4550_, v_bs_4551_);
stack->m_obj
 = v_res_4582_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___boxed(lean_object* v___x_4583_, lean_object* v_sz_4584_, lean_object* v_i_4585_, lean_object* v_bs_4586_){
_start:
{
size_t v_sz_boxed_4587_; size_t v_i_boxed_4588_; lean_object* v_res_4589_; 
v_sz_boxed_4587_ = lean_unbox_usize(v_sz_4584_);
lean_dec(v_sz_4584_);
v_i_boxed_4588_ = lean_unbox_usize(v_i_4585_);
lean_dec(v_i_4585_);
v_res_4589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4583_, v_sz_boxed_4587_, v_i_boxed_4588_, v_bs_4586_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(lean_object* v_x_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_){
_start:
{
lean_object* v___x_4605_; uint8_t v___x_4606_; 
v___x_4605_ = ((lean_object*)(l_Lean_solveTactic___closed__1));
lean_inc(v_x_4602_);
v___x_4606_ = l_Lean_Syntax_isOfKind(v_x_4602_, v___x_4605_);
if (v___x_4606_ == 0)
{
lean_object* v___x_4607_; lean_object* v___x_4608_; 
lean_dec(v_x_4602_);
v___x_4607_ = lean_box(1);
v___x_4608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4608_, 0, v___x_4607_);
lean_ctor_set(v___x_4608_, 1, v_a_4604_);
return v___x_4608_;
}
else
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; size_t v_sz_4612_; size_t v___x_4613_; lean_object* v___x_4614_; 
v___x_4609_ = lean_unsigned_to_nat(1u);
v___x_4610_ = l_Lean_Syntax_getArg(v_x_4602_, v___x_4609_);
lean_dec(v_x_4602_);
v___x_4611_ = l_Lean_Syntax_getArgs(v___x_4610_);
lean_dec(v___x_4610_);
v_sz_4612_ = lean_array_size(v___x_4611_);
v___x_4613_ = ((size_t)0ULL);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_4612_, v___x_4613_, v___x_4611_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_box(1);
v___x_4616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4616_, 0, v___x_4615_);
lean_ctor_set(v___x_4616_, 1, v_a_4604_);
return v___x_4616_;
}
else
{
lean_object* v_val_4617_; lean_object* v_ref_4618_; uint8_t v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; size_t v_sz_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_val_4617_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_val_4617_);
lean_dec_ref_known(v___x_4614_, 1);
v_ref_4618_ = lean_ctor_get(v_a_4603_, 5);
v___x_4619_ = 0;
v___x_4620_ = l_Lean_SourceInfo_fromRef(v_ref_4618_, v___x_4619_);
v___x_4621_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0));
v___x_4622_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1));
lean_inc_n(v___x_4620_, 8);
v___x_4623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4623_, 0, v___x_4620_);
lean_ctor_set(v___x_4623_, 1, v___x_4621_);
v___x_4624_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_4625_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4626_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4627_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2));
v___x_4628_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3));
v___x_4629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4620_);
lean_ctor_set(v___x_4629_, 1, v___x_4627_);
v___x_4630_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4631_ = lean_array_size(v_val_4617_);
v___x_4632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4620_, v_sz_4631_, v___x_4613_, v_val_4617_);
v___x_4633_ = l_Array_append___redArg(v___x_4630_, v___x_4632_);
lean_dec_ref(v___x_4632_);
v___x_4634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4634_, 0, v___x_4620_);
lean_ctor_set(v___x_4634_, 1, v___x_4626_);
lean_ctor_set(v___x_4634_, 2, v___x_4633_);
v___x_4635_ = l_Lean_Syntax_node2(v___x_4620_, v___x_4628_, v___x_4629_, v___x_4634_);
v___x_4636_ = l_Lean_Syntax_node1(v___x_4620_, v___x_4626_, v___x_4635_);
v___x_4637_ = l_Lean_Syntax_node1(v___x_4620_, v___x_4625_, v___x_4636_);
v___x_4638_ = l_Lean_Syntax_node1(v___x_4620_, v___x_4624_, v___x_4637_);
v___x_4639_ = l_Lean_Syntax_node2(v___x_4620_, v___x_4622_, v___x_4623_, v___x_4638_);
v___x_4640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4640_, 0, v___x_4639_);
lean_ctor_set(v___x_4640_, 1, v_a_4604_);
return v___x_4640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___boxed(lean_object* v_x_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v_res_4644_; 
v_res_4644_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(v_x_4641_, v_a_4642_, v_a_4643_);
lean_dec_ref(v_a_4642_);
return v_res_4644_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(lean_object* v___x_4673_, size_t v_sz_4674_, size_t v_i_4675_, lean_object* v_bs_4676_){
_start:
{
uint8_t v___x_4677_; 
v___x_4677_ = lean_usize_dec_lt(v_i_4675_, v_sz_4674_);
if (v___x_4677_ == 0)
{
lean_dec(v___x_4673_);
return v_bs_4676_;
}
else
{
lean_object* v___x_4678_; lean_object* v_v_4679_; lean_object* v___x_4680_; lean_object* v_bs_x27_4681_; lean_object* v___x_4682_; size_t v___x_4683_; size_t v___x_4684_; lean_object* v___x_4685_; 
v___x_4678_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v_v_4679_ = lean_array_uget(v_bs_4676_, v_i_4675_);
v___x_4680_ = lean_unsigned_to_nat(0u);
v_bs_x27_4681_ = lean_array_uset(v_bs_4676_, v_i_4675_, v___x_4680_);
lean_inc(v___x_4673_);
v___x_4682_ = l_Lean_Syntax_node1(v___x_4673_, v___x_4678_, v_v_4679_);
v___x_4683_ = ((size_t)1ULL);
v___x_4684_ = lean_usize_add(v_i_4675_, v___x_4683_);
v___x_4685_ = lean_array_uset(v_bs_x27_4681_, v_i_4675_, v___x_4682_);
v_i_4675_ = v___x_4684_;
v_bs_4676_ = v___x_4685_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4673_ = stack[0].m_obj;
size_t v_sz_4674_ = stack[1].m_num;
size_t v_i_4675_ = stack[2].m_num;
lean_object* v_bs_4676_ = stack[3].m_obj;
lean_object* v_res_4687_;
v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4673_, v_sz_4674_, v_i_4675_, v_bs_4676_);
stack->m_obj
 = v_res_4687_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0___boxed(lean_object* v___x_4688_, lean_object* v_sz_4689_, lean_object* v_i_4690_, lean_object* v_bs_4691_){
_start:
{
size_t v_sz_boxed_4692_; size_t v_i_boxed_4693_; lean_object* v_res_4694_; 
v_sz_boxed_4692_ = lean_unbox_usize(v_sz_4689_);
lean_dec(v_sz_4689_);
v_i_boxed_4693_ = lean_unbox_usize(v_i_4690_);
lean_dec(v_i_4690_);
v_res_4694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4688_, v_sz_boxed_4692_, v_i_boxed_4693_, v_bs_4691_);
return v_res_4694_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11(void){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4729_ = l_Lean_mkAtom(v___x_4728_);
return v___x_4729_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12));
v___x_4732_ = l_String_toRawSubstring_x27(v___x_4731_);
return v___x_4732_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20(void){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19));
v___x_4747_ = l_String_toRawSubstring_x27(v___x_4746_);
return v___x_4747_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25(void){
_start:
{
lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4759_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15));
v___x_4760_ = l_String_toRawSubstring_x27(v___x_4759_);
return v___x_4760_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(lean_object* v_x_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v___x_4777_; uint8_t v___x_4778_; 
v___x_4777_ = ((lean_object*)(l_Lean_term__Matches___x7c___closed__1));
lean_inc(v_x_4774_);
v___x_4778_ = l_Lean_Syntax_isOfKind(v_x_4774_, v___x_4777_);
if (v___x_4778_ == 0)
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
lean_dec(v_x_4774_);
v___x_4779_ = lean_box(1);
v___x_4780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
lean_ctor_set(v___x_4780_, 1, v_a_4776_);
return v___x_4780_;
}
else
{
lean_object* v_quotContext_4781_; lean_object* v_currMacroScope_4782_; lean_object* v_ref_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v_p_4788_; uint8_t v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; size_t v_sz_4820_; size_t v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
v_quotContext_4781_ = lean_ctor_get(v_a_4775_, 1);
v_currMacroScope_4782_ = lean_ctor_get(v_a_4775_, 2);
v_ref_4783_ = lean_ctor_get(v_a_4775_, 5);
v___x_4784_ = lean_unsigned_to_nat(0u);
v___x_4785_ = l_Lean_Syntax_getArg(v_x_4774_, v___x_4784_);
v___x_4786_ = lean_unsigned_to_nat(2u);
v___x_4787_ = l_Lean_Syntax_getArg(v_x_4774_, v___x_4786_);
lean_dec(v_x_4774_);
v_p_4788_ = l_Lean_Syntax_getArgs(v___x_4787_);
lean_dec(v___x_4787_);
v___x_4789_ = 0;
v___x_4790_ = l_Lean_SourceInfo_fromRef(v_ref_4783_, v___x_4789_);
v___x_4791_ = ((lean_object*)(l_unexpandExists___closed__1));
v___x_4792_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_4793_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_4790_, 29);
v___x_4794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4790_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_4796_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_4797_ = lean_box(0);
lean_inc_n(v_currMacroScope_4782_, 4);
lean_inc_n(v_quotContext_4781_, 4);
v___x_4798_ = l_Lean_addMacroScope(v_quotContext_4781_, v___x_4797_, v_currMacroScope_4782_);
v___x_4799_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0));
v___x_4800_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4790_);
lean_ctor_set(v___x_4800_, 1, v___x_4796_);
lean_ctor_set(v___x_4800_, 2, v___x_4798_);
lean_ctor_set(v___x_4800_, 3, v___x_4799_);
v___x_4801_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4795_, v___x_4800_);
v___x_4802_ = l_Lean_Syntax_node2(v___x_4790_, v___x_4792_, v___x_4794_, v___x_4801_);
v___x_4803_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1));
v___x_4804_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2));
v___x_4805_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3));
v___x_4806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4790_);
lean_ctor_set(v___x_4806_, 1, v___x_4804_);
v___x_4807_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4808_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4809_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4790_);
lean_ctor_set(v___x_4809_, 1, v___x_4807_);
lean_ctor_set(v___x_4809_, 2, v___x_4808_);
v___x_4810_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5));
lean_inc_ref_n(v___x_4809_, 2);
v___x_4811_ = l_Lean_Syntax_node2(v___x_4790_, v___x_4810_, v___x_4809_, v___x_4785_);
v___x_4812_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4807_, v___x_4811_);
v___x_4813_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6));
v___x_4814_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4814_, 0, v___x_4790_);
lean_ctor_set(v___x_4814_, 1, v___x_4813_);
v___x_4815_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8));
v___x_4816_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10));
v___x_4817_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4790_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_p_4788_);
lean_dec_ref(v_p_4788_);
v_sz_4820_ = lean_array_size(v___x_4819_);
v___x_4821_ = ((size_t)0ULL);
v___x_4822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4790_, v_sz_4820_, v___x_4821_, v___x_4819_);
v___x_4823_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11);
v___x_4824_ = l_Lean_mkSepArray(v___x_4822_, v___x_4823_);
lean_dec_ref(v___x_4822_);
v___x_4825_ = l_Array_append___redArg(v___x_4808_, v___x_4824_);
lean_dec_ref(v___x_4824_);
v___x_4826_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4790_);
lean_ctor_set(v___x_4826_, 1, v___x_4807_);
lean_ctor_set(v___x_4826_, 2, v___x_4825_);
v___x_4827_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_4828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4790_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13);
v___x_4830_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14));
v___x_4831_ = l_Lean_addMacroScope(v_quotContext_4781_, v___x_4830_, v_currMacroScope_4782_);
v___x_4832_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18));
v___x_4833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4790_);
lean_ctor_set(v___x_4833_, 1, v___x_4829_);
lean_ctor_set(v___x_4833_, 2, v___x_4831_);
lean_ctor_set(v___x_4833_, 3, v___x_4832_);
lean_inc_ref(v___x_4828_);
lean_inc_ref(v___x_4818_);
v___x_4834_ = l_Lean_Syntax_node4(v___x_4790_, v___x_4816_, v___x_4818_, v___x_4826_, v___x_4828_, v___x_4833_);
v___x_4835_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11));
v___x_4836_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_4837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4837_, 0, v___x_4790_);
lean_ctor_set(v___x_4837_, 1, v___x_4836_);
v___x_4838_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4835_, v___x_4837_);
v___x_4839_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4807_, v___x_4838_);
v___x_4840_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4807_, v___x_4839_);
v___x_4841_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20);
v___x_4842_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21));
v___x_4843_ = l_Lean_addMacroScope(v_quotContext_4781_, v___x_4842_, v_currMacroScope_4782_);
v___x_4844_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24));
v___x_4845_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4790_);
lean_ctor_set(v___x_4845_, 1, v___x_4841_);
lean_ctor_set(v___x_4845_, 2, v___x_4843_);
lean_ctor_set(v___x_4845_, 3, v___x_4844_);
v___x_4846_ = l_Lean_Syntax_node4(v___x_4790_, v___x_4816_, v___x_4818_, v___x_4840_, v___x_4828_, v___x_4845_);
v___x_4847_ = l_Lean_Syntax_node2(v___x_4790_, v___x_4807_, v___x_4834_, v___x_4846_);
v___x_4848_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4815_, v___x_4847_);
v___x_4849_ = l_Lean_Syntax_node6(v___x_4790_, v___x_4805_, v___x_4806_, v___x_4809_, v___x_4809_, v___x_4812_, v___x_4814_, v___x_4848_);
v___x_4850_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4790_);
lean_ctor_set(v___x_4851_, 1, v___x_4850_);
lean_inc_ref(v___x_4851_);
lean_inc(v___x_4802_);
v___x_4852_ = l_Lean_Syntax_node3(v___x_4790_, v___x_4803_, v___x_4802_, v___x_4849_, v___x_4851_);
v___x_4853_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_4854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4790_);
lean_ctor_set(v___x_4854_, 1, v___x_4853_);
v___x_4855_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25);
v___x_4856_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26));
v___x_4857_ = l_Lean_addMacroScope(v_quotContext_4781_, v___x_4856_, v_currMacroScope_4782_);
v___x_4858_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30));
v___x_4859_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4790_);
lean_ctor_set(v___x_4859_, 1, v___x_4855_);
lean_ctor_set(v___x_4859_, 2, v___x_4857_);
lean_ctor_set(v___x_4859_, 3, v___x_4858_);
v___x_4860_ = l_Lean_Syntax_node1(v___x_4790_, v___x_4807_, v___x_4859_);
v___x_4861_ = l_Lean_Syntax_node5(v___x_4790_, v___x_4791_, v___x_4802_, v___x_4852_, v___x_4854_, v___x_4860_, v___x_4851_);
v___x_4862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
lean_ctor_set(v___x_4862_, 1, v_a_4776_);
return v___x_4862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___boxed(lean_object* v_x_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_){
_start:
{
lean_object* v_res_4866_; 
v_res_4866_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(v_x_4863_, v_a_4864_, v_a_4865_);
lean_dec_ref(v_a_4864_);
return v_res_4866_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1(void){
_start:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0));
v___x_4897_ = l_String_toRawSubstring_x27(v___x_4896_);
return v___x_4897_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4911_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7));
v___x_4912_ = l_String_toRawSubstring_x27(v___x_4911_);
return v___x_4912_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(lean_object* v_x_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
lean_object* v___x_4928_; uint8_t v___x_4929_; 
v___x_4928_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v_x_4925_);
v___x_4929_ = l_Lean_Syntax_isOfKind(v_x_4925_, v___x_4928_);
if (v___x_4929_ == 0)
{
lean_object* v___x_4930_; lean_object* v___x_4931_; 
lean_dec(v_x_4925_);
v___x_4930_ = lean_box(1);
v___x_4931_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4931_, 0, v___x_4930_);
lean_ctor_set(v___x_4931_, 1, v_a_4927_);
return v___x_4931_;
}
else
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; uint8_t v___x_4935_; 
v___x_4932_ = lean_unsigned_to_nat(0u);
v___x_4933_ = lean_unsigned_to_nat(1u);
v___x_4934_ = l_Lean_Syntax_getArg(v_x_4925_, v___x_4933_);
lean_dec(v_x_4925_);
lean_inc(v___x_4934_);
v___x_4935_ = l_Lean_Syntax_matchesNull(v___x_4934_, v___x_4933_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4936_ = lean_unsigned_to_nat(2u);
v___x_4937_ = l_Lean_Syntax_getNumArgs(v___x_4934_);
v___x_4938_ = lean_nat_dec_le(v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_dec(v___x_4937_);
lean_dec(v___x_4934_);
v___x_4939_ = lean_box(1);
v___x_4940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
lean_ctor_set(v___x_4940_, 1, v_a_4927_);
return v___x_4940_;
}
else
{
lean_object* v_quotContext_4941_; lean_object* v_currMacroScope_4942_; lean_object* v_ref_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v_quotContext_4941_ = lean_ctor_get(v_a_4926_, 1);
v_currMacroScope_4942_ = lean_ctor_get(v_a_4926_, 2);
v_ref_4943_ = lean_ctor_get(v_a_4926_, 5);
v___x_4944_ = l_Lean_Syntax_getArg(v___x_4934_, v___x_4932_);
v___x_4945_ = l_Lean_Syntax_getArgs(v___x_4934_);
lean_dec(v___x_4934_);
v___x_4946_ = l_Array_extract___redArg(v___x_4945_, v___x_4936_, v___x_4937_);
lean_dec_ref(v___x_4945_);
v___x_4947_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4948_ = lean_box(2);
v___x_4949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4948_);
lean_ctor_set(v___x_4949_, 1, v___x_4947_);
lean_ctor_set(v___x_4949_, 2, v___x_4946_);
v___x_4950_ = l_Lean_Syntax_getArgs(v___x_4949_);
lean_dec_ref_known(v___x_4949_, 3);
v___x_4951_ = l_Lean_SourceInfo_fromRef(v_ref_4943_, v___x_4935_);
v___x_4952_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4953_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1);
v___x_4954_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2));
lean_inc(v_currMacroScope_4942_);
lean_inc(v_quotContext_4941_);
v___x_4955_ = l_Lean_addMacroScope(v_quotContext_4941_, v___x_4954_, v_currMacroScope_4942_);
v___x_4956_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6));
lean_inc_n(v___x_4951_, 6);
v___x_4957_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4957_, 0, v___x_4951_);
lean_ctor_set(v___x_4957_, 1, v___x_4953_);
lean_ctor_set(v___x_4957_, 2, v___x_4955_);
lean_ctor_set(v___x_4957_, 3, v___x_4956_);
v___x_4958_ = ((lean_object*)(l_unexpandSubtype___closed__2));
v___x_4959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4959_, 0, v___x_4951_);
lean_ctor_set(v___x_4959_, 1, v___x_4958_);
v___x_4960_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4961_ = l_Array_append___redArg(v___x_4960_, v___x_4950_);
lean_dec_ref(v___x_4950_);
v___x_4962_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4962_, 0, v___x_4951_);
lean_ctor_set(v___x_4962_, 1, v___x_4947_);
lean_ctor_set(v___x_4962_, 2, v___x_4961_);
v___x_4963_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4951_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
v___x_4965_ = l_Lean_Syntax_node3(v___x_4951_, v___x_4928_, v___x_4959_, v___x_4962_, v___x_4964_);
v___x_4966_ = l_Lean_Syntax_node2(v___x_4951_, v___x_4947_, v___x_4944_, v___x_4965_);
v___x_4967_ = l_Lean_Syntax_node2(v___x_4951_, v___x_4952_, v___x_4957_, v___x_4966_);
v___x_4968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
lean_ctor_set(v___x_4968_, 1, v_a_4927_);
return v___x_4968_;
}
}
else
{
lean_object* v_quotContext_4969_; lean_object* v_currMacroScope_4970_; lean_object* v_ref_4971_; lean_object* v___x_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; 
v_quotContext_4969_ = lean_ctor_get(v_a_4926_, 1);
v_currMacroScope_4970_ = lean_ctor_get(v_a_4926_, 2);
v_ref_4971_ = lean_ctor_get(v_a_4926_, 5);
v___x_4972_ = l_Lean_Syntax_getArg(v___x_4934_, v___x_4932_);
lean_dec(v___x_4934_);
v___x_4973_ = 0;
v___x_4974_ = l_Lean_SourceInfo_fromRef(v_ref_4971_, v___x_4973_);
v___x_4975_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4976_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8);
v___x_4977_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9));
lean_inc(v_currMacroScope_4970_);
lean_inc(v_quotContext_4969_);
v___x_4978_ = l_Lean_addMacroScope(v_quotContext_4969_, v___x_4977_, v_currMacroScope_4970_);
v___x_4979_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13));
lean_inc_n(v___x_4974_, 2);
v___x_4980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4974_);
lean_ctor_set(v___x_4980_, 1, v___x_4976_);
lean_ctor_set(v___x_4980_, 2, v___x_4978_);
lean_ctor_set(v___x_4980_, 3, v___x_4979_);
v___x_4981_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4982_ = l_Lean_Syntax_node1(v___x_4974_, v___x_4981_, v___x_4972_);
v___x_4983_ = l_Lean_Syntax_node2(v___x_4974_, v___x_4975_, v___x_4980_, v___x_4982_);
v___x_4984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
lean_ctor_set(v___x_4984_, 1, v_a_4927_);
return v___x_4984_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___boxed(lean_object* v_x_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(v_x_4985_, v_a_4986_, v_a_4987_);
lean_dec_ref(v_a_4986_);
return v_res_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander(lean_object* v_x_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_){
_start:
{
lean_object* v___x_4992_; uint8_t v___x_4993_; 
v___x_4992_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_4989_);
v___x_4993_ = l_Lean_Syntax_isOfKind(v_x_4989_, v___x_4992_);
if (v___x_4993_ == 0)
{
lean_object* v___x_4994_; lean_object* v___x_4995_; 
lean_dec(v_x_4989_);
v___x_4994_ = lean_box(0);
v___x_4995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
lean_ctor_set(v___x_4995_, 1, v_a_4991_);
return v___x_4995_;
}
else
{
lean_object* v___x_4996_; lean_object* v___x_4997_; uint8_t v___x_4998_; 
v___x_4996_ = lean_unsigned_to_nat(1u);
v___x_4997_ = l_Lean_Syntax_getArg(v_x_4989_, v___x_4996_);
lean_dec(v_x_4989_);
lean_inc(v___x_4997_);
v___x_4998_ = l_Lean_Syntax_matchesNull(v___x_4997_, v___x_4996_);
if (v___x_4998_ == 0)
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_dec(v___x_4997_);
v___x_4999_ = lean_box(0);
v___x_5000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
lean_ctor_set(v___x_5000_, 1, v_a_4991_);
return v___x_5000_;
}
else
{
lean_object* v___x_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5001_ = lean_unsigned_to_nat(0u);
v___x_5002_ = l_Lean_Syntax_getArg(v___x_4997_, v___x_5001_);
lean_dec(v___x_4997_);
v___x_5003_ = 0;
v___x_5004_ = l_Lean_SourceInfo_fromRef(v_a_4990_, v___x_5003_);
v___x_5005_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
v___x_5006_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_5004_, 3);
v___x_5007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5007_, 0, v___x_5004_);
lean_ctor_set(v___x_5007_, 1, v___x_5006_);
v___x_5008_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_5009_ = l_Lean_Syntax_node1(v___x_5004_, v___x_5008_, v___x_5002_);
v___x_5010_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_5011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5011_, 0, v___x_5004_);
lean_ctor_set(v___x_5011_, 1, v___x_5010_);
v___x_5012_ = l_Lean_Syntax_node3(v___x_5004_, v___x_5005_, v___x_5007_, v___x_5009_, v___x_5011_);
v___x_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5012_);
lean_ctor_set(v___x_5013_, 1, v_a_4991_);
return v___x_5013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander___boxed(lean_object* v_x_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
lean_object* v_res_5017_; 
v_res_5017_ = l_Lean_singletonUnexpander(v_x_5014_, v_a_5015_, v_a_5016_);
lean_dec(v_a_5015_);
return v_res_5017_;
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander(lean_object* v_x_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_){
_start:
{
lean_object* v___x_5021_; uint8_t v___x_5022_; 
v___x_5021_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_5018_);
v___x_5022_ = l_Lean_Syntax_isOfKind(v_x_5018_, v___x_5021_);
if (v___x_5022_ == 0)
{
lean_object* v___x_5023_; lean_object* v___x_5024_; 
lean_dec(v_x_5018_);
v___x_5023_ = lean_box(0);
v___x_5024_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5023_);
lean_ctor_set(v___x_5024_, 1, v_a_5020_);
return v___x_5024_;
}
else
{
lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; uint8_t v___x_5028_; 
v___x_5025_ = lean_unsigned_to_nat(1u);
v___x_5026_ = l_Lean_Syntax_getArg(v_x_5018_, v___x_5025_);
lean_dec(v_x_5018_);
v___x_5027_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_5026_);
v___x_5028_ = l_Lean_Syntax_matchesNull(v___x_5026_, v___x_5027_);
if (v___x_5028_ == 0)
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
lean_dec(v___x_5026_);
v___x_5029_ = lean_box(0);
v___x_5030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5029_);
lean_ctor_set(v___x_5030_, 1, v_a_5020_);
return v___x_5030_;
}
else
{
lean_object* v___x_5031_; lean_object* v___x_5032_; uint8_t v___x_5033_; 
v___x_5031_ = l_Lean_Syntax_getArg(v___x_5026_, v___x_5025_);
v___x_5032_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v___x_5031_);
v___x_5033_ = l_Lean_Syntax_isOfKind(v___x_5031_, v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; lean_object* v___x_5035_; 
lean_dec(v___x_5031_);
lean_dec(v___x_5026_);
v___x_5034_ = lean_box(0);
v___x_5035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5034_);
lean_ctor_set(v___x_5035_, 1, v_a_5020_);
return v___x_5035_;
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5036_ = lean_unsigned_to_nat(0u);
v___x_5037_ = l_Lean_Syntax_getArg(v___x_5026_, v___x_5036_);
lean_dec(v___x_5026_);
v___x_5038_ = l_Lean_Syntax_getArg(v___x_5031_, v___x_5025_);
lean_dec(v___x_5031_);
v___x_5039_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_5040_ = l_Lean_Syntax_getArgs(v___x_5038_);
lean_dec(v___x_5038_);
v___x_5041_ = 0;
v___x_5042_ = l_Lean_SourceInfo_fromRef(v_a_5019_, v___x_5041_);
v___x_5043_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_5042_, 4);
v___x_5044_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5042_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
v___x_5045_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_5046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5046_, 0, v___x_5042_);
lean_ctor_set(v___x_5046_, 1, v___x_5039_);
v___x_5047_ = l_Array_mkArray2___redArg(v___x_5037_, v___x_5046_);
v___x_5048_ = l_Array_append___redArg(v___x_5047_, v___x_5040_);
lean_dec_ref(v___x_5040_);
v___x_5049_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5042_);
lean_ctor_set(v___x_5049_, 1, v___x_5045_);
lean_ctor_set(v___x_5049_, 2, v___x_5048_);
v___x_5050_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_5051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5042_);
lean_ctor_set(v___x_5051_, 1, v___x_5050_);
v___x_5052_ = l_Lean_Syntax_node3(v___x_5042_, v___x_5032_, v___x_5044_, v___x_5049_, v___x_5051_);
v___x_5053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5052_);
lean_ctor_set(v___x_5053_, 1, v_a_5020_);
return v___x_5053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander___boxed(lean_object* v_x_5054_, lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Lean_insertUnexpander(v_x_5054_, v_a_5055_, v_a_5056_);
lean_dec(v_a_5055_);
return v_res_5057_;
}
}
lean_object* runtime_initialize_Init_Conv(uint8_t builtin);
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_NotationExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
