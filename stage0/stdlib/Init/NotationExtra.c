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
uint8_t v___x_806__boxed_380_; size_t v_i_boxed_381_; size_t v_stop_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v___x_806__boxed_380_ = lean_unbox(v___x_376_);
v_i_boxed_381_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_stop_boxed_382_ = lean_unbox_usize(v_stop_379_);
lean_dec(v_stop_379_);
v_res_383_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_expandExplicitBinders_spec__0(v___x_806__boxed_380_, v_as_377_, v_i_boxed_381_, v_stop_boxed_382_);
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
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_399_);
lean_dec(v___x_393_);
lean_dec(v_body_388_);
v___x_408_ = ((lean_object*)(l_Lean_expandExplicitBinders___closed__0));
v___x_409_ = l_Lean_Macro_throwError___redArg(v___x_408_, v_a_389_, v_a_390_);
return v___x_409_;
}
}
}
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_410_ = l_Lean_Syntax_getArg(v___x_395_, v___x_394_);
v___x_411_ = l_Lean_Syntax_getArgs(v___x_410_);
lean_dec(v___x_410_);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = l_Lean_Syntax_getArg(v___x_395_, v___x_412_);
lean_dec(v___x_395_);
v___x_414_ = l_Lean_Syntax_isNone(v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = l_Lean_Syntax_getArg(v___x_413_, v___x_412_);
lean_dec(v___x_413_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
v___x_417_ = l_Lean_expandExplicitBindersAux(v___x_393_, v___x_411_, v___x_416_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_411_);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v___x_413_);
v___x_418_ = lean_box(0);
v___x_419_ = l_Lean_expandExplicitBindersAux(v___x_393_, v___x_411_, v___x_418_, v_body_388_, v_a_389_, v_a_390_);
lean_dec_ref(v___x_411_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_expandExplicitBinders___boxed(lean_object* v_combinatorDeclName_420_, lean_object* v_explicitBinders_421_, lean_object* v_body_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_expandExplicitBinders(v_combinatorDeclName_420_, v_explicitBinders_421_, v_body_422_, v_a_423_, v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_explicitBinders_421_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders(lean_object* v_combinatorDeclName_426_, lean_object* v_bracketedExplicitBinders_427_, lean_object* v_body_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_ref_431_; uint8_t v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_ref_431_ = lean_ctor_get(v_a_429_, 5);
v___x_432_ = 0;
v___x_433_ = l_Lean_mkCIdentFrom(v_ref_431_, v_combinatorDeclName_426_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___x_436_ = lean_array_push(v___x_435_, v_bracketedExplicitBinders_427_);
v___x_437_ = l_Lean_expandBracketedBindersAux(v___x_433_, v___x_436_, v_body_428_, v_a_429_, v_a_430_);
lean_dec_ref(v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_expandBracketedBinders___boxed(lean_object* v_combinatorDeclName_438_, lean_object* v_bracketedExplicitBinders_439_, lean_object* v_body_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_expandBracketedBinders(v_combinatorDeclName_438_, v_bracketedExplicitBinders_439_, v_body_440_, v_a_441_, v_a_442_);
lean_dec_ref(v_a_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(lean_object* v_____do__lift_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = 0;
v___x_651_ = l_Lean_SourceInfo_fromRef(v_____do__lift_647_, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___y_649_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0___boxed(lean_object* v_____do__lift_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_____do__lift_653_, v___y_654_, v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v_____do__lift_653_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(size_t v_sz_657_, size_t v_i_658_, lean_object* v_bs_659_){
_start:
{
uint8_t v___x_660_; 
v___x_660_ = lean_usize_dec_lt(v_i_658_, v_sz_657_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_bs_659_);
return v___x_661_;
}
else
{
lean_object* v_v_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_v_662_ = lean_array_uget_borrowed(v_bs_659_, v_i_658_);
v___x_663_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__1));
lean_inc(v_v_662_);
v___x_664_ = l_Lean_Syntax_isOfKind(v_v_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_dec_ref(v_bs_659_);
v___x_665_ = lean_box(0);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = l_Lean_Syntax_getArg(v_v_662_, v___x_666_);
v___x_668_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_667_);
v___x_669_ = l_Lean_Syntax_isOfKind(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_667_);
lean_dec_ref(v_bs_659_);
v___x_670_ = lean_box(0);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = l_Lean_Syntax_getArg(v_v_662_, v___x_671_);
v___x_673_ = l_Lean_Syntax_matchesNull(v___x_672_, v___x_666_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_dec(v___x_667_);
lean_dec_ref(v_bs_659_);
v___x_674_ = lean_box(0);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v_bs_x27_676_; lean_object* v_cs_u2081_677_; lean_object* v_cs_u2082_678_; lean_object* v___x_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___x_675_ = lean_unsigned_to_nat(2u);
v_bs_x27_676_ = lean_array_uset(v_bs_659_, v_i_658_, v___x_666_);
v_cs_u2081_677_ = l_Lean_Syntax_getArg(v___x_667_, v___x_666_);
v_cs_u2082_678_ = l_Lean_Syntax_getArg(v___x_667_, v___x_675_);
lean_dec(v___x_667_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_cs_u2081_677_);
lean_ctor_set(v___x_679_, 1, v_cs_u2082_678_);
v___x_680_ = ((size_t)1ULL);
v___x_681_ = lean_usize_add(v_i_658_, v___x_680_);
v___x_682_ = lean_array_uset(v_bs_x27_676_, v_i_658_, v___x_679_);
v_i_658_ = v___x_681_;
v_bs_659_ = v___x_682_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0___boxed(lean_object* v_sz_684_, lean_object* v_i_685_, lean_object* v_bs_686_){
_start:
{
size_t v_sz_boxed_687_; size_t v_i_boxed_688_; lean_object* v_res_689_; 
v_sz_boxed_687_ = lean_unbox_usize(v_sz_684_);
lean_dec(v_sz_684_);
v_i_boxed_688_ = lean_unbox_usize(v_i_685_);
lean_dec(v_i_685_);
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_boxed_687_, v_i_boxed_688_, v_bs_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(lean_object* v_as_701_, size_t v_sz_702_, size_t v_i_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
uint8_t v___x_707_; 
v___x_707_ = lean_usize_dec_lt(v_i_703_, v_sz_702_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; 
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v_b_704_);
lean_ctor_set(v___x_708_, 1, v___y_706_);
return v___x_708_;
}
else
{
lean_object* v_a_709_; lean_object* v_fst_710_; lean_object* v_snd_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_731_; 
v_a_709_ = lean_array_uget(v_as_701_, v_i_703_);
v_fst_710_ = lean_ctor_get(v_a_709_, 0);
v_snd_711_ = lean_ctor_get(v_a_709_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_709_);
if (v_isSharedCheck_731_ == 0)
{
v___x_713_ = v_a_709_;
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snd_711_);
lean_inc(v_fst_710_);
lean_dec(v_a_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_731_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v_ref_715_; uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v_ref_715_ = lean_ctor_get(v___y_705_, 5);
v___x_716_ = 0;
v___x_717_ = l_Lean_SourceInfo_fromRef(v_ref_715_, v___x_716_);
v___x_718_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__1));
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v___x_717_);
if (v_isShared_714_ == 0)
{
lean_ctor_set_tag(v___x_713_, 2);
lean_ctor_set(v___x_713_, 1, v___x_720_);
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_722_ = v___x_713_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_730_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; size_t v___x_727_; size_t v___x_728_; 
lean_inc_n(v___x_717_, 2);
v___x_723_ = l_Lean_Syntax_node3(v___x_717_, v___x_719_, v_fst_710_, v___x_722_, v_snd_711_);
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__5));
v___x_725_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_717_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = l_Lean_Syntax_node3(v___x_717_, v___x_718_, v___x_723_, v___x_725_, v_b_704_);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_703_, v___x_727_);
v_i_703_ = v___x_728_;
v_b_704_ = v___x_726_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___boxed(lean_object* v_as_732_, lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_b_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
size_t v_sz_boxed_738_; size_t v_i_boxed_739_; lean_object* v_res_740_; 
v_sz_boxed_738_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_739_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v_as_732_, v_sz_boxed_738_, v_i_boxed_739_, v_b_735_, v___y_736_, v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec_ref(v_as_732_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(size_t v_sz_741_, size_t v_i_742_, lean_object* v_bs_743_){
_start:
{
uint8_t v___x_744_; 
v___x_744_ = lean_usize_dec_lt(v_i_742_, v_sz_741_);
if (v___x_744_ == 0)
{
return v_bs_743_;
}
else
{
lean_object* v_v_745_; lean_object* v___x_746_; lean_object* v_bs_x27_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v_v_745_ = lean_array_uget(v_bs_743_, v_i_742_);
v___x_746_ = lean_unsigned_to_nat(0u);
v_bs_x27_747_ = lean_array_uset(v_bs_743_, v_i_742_, v___x_746_);
v___x_748_ = ((size_t)1ULL);
v___x_749_ = lean_usize_add(v_i_742_, v___x_748_);
v___x_750_ = lean_array_uset(v_bs_x27_747_, v_i_742_, v_v_745_);
v_i_742_ = v___x_749_;
v_bs_743_ = v___x_750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5___boxed(lean_object* v_sz_752_, lean_object* v_i_753_, lean_object* v_bs_754_){
_start:
{
size_t v_sz_boxed_755_; size_t v_i_boxed_756_; lean_object* v_res_757_; 
v_sz_boxed_755_ = lean_unbox_usize(v_sz_752_);
lean_dec(v_sz_752_);
v_i_boxed_756_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_boxed_755_, v_i_boxed_756_, v_bs_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(size_t v_sz_758_, size_t v_i_759_, lean_object* v_bs_760_){
_start:
{
uint8_t v___x_761_; 
v___x_761_ = lean_usize_dec_lt(v_i_759_, v_sz_758_);
if (v___x_761_ == 0)
{
return v_bs_760_;
}
else
{
lean_object* v_v_762_; lean_object* v___x_763_; lean_object* v_bs_x27_764_; size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v_v_762_ = lean_array_uget(v_bs_760_, v_i_759_);
v___x_763_ = lean_unsigned_to_nat(0u);
v_bs_x27_764_ = lean_array_uset(v_bs_760_, v_i_759_, v___x_763_);
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_759_, v___x_765_);
v___x_767_ = lean_array_uset(v_bs_x27_764_, v_i_759_, v_v_762_);
v_i_759_ = v___x_766_;
v_bs_760_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4___boxed(lean_object* v_sz_769_, lean_object* v_i_770_, lean_object* v_bs_771_){
_start:
{
size_t v_sz_boxed_772_; size_t v_i_boxed_773_; lean_object* v_res_774_; 
v_sz_boxed_772_ = lean_unbox_usize(v_sz_769_);
lean_dec(v_sz_769_);
v_i_boxed_773_ = lean_unbox_usize(v_i_770_);
lean_dec(v_i_770_);
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_boxed_772_, v_i_boxed_773_, v_bs_771_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(size_t v_sz_775_, size_t v_i_776_, lean_object* v_bs_777_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_lt(v_i_776_, v_sz_775_);
if (v___x_778_ == 0)
{
return v_bs_777_;
}
else
{
lean_object* v_v_779_; lean_object* v_fst_780_; lean_object* v___x_781_; lean_object* v_bs_x27_782_; size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v_v_779_ = lean_array_uget_borrowed(v_bs_777_, v_i_776_);
v_fst_780_ = lean_ctor_get(v_v_779_, 0);
lean_inc(v_fst_780_);
v___x_781_ = lean_unsigned_to_nat(0u);
v_bs_x27_782_ = lean_array_uset(v_bs_777_, v_i_776_, v___x_781_);
v___x_783_ = ((size_t)1ULL);
v___x_784_ = lean_usize_add(v_i_776_, v___x_783_);
v___x_785_ = lean_array_uset(v_bs_x27_782_, v_i_776_, v_fst_780_);
v_i_776_ = v___x_784_;
v_bs_777_ = v___x_785_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2___boxed(lean_object* v_sz_787_, lean_object* v_i_788_, lean_object* v_bs_789_){
_start:
{
size_t v_sz_boxed_790_; size_t v_i_boxed_791_; lean_object* v_res_792_; 
v_sz_boxed_790_ = lean_unbox_usize(v_sz_787_);
lean_dec(v_sz_787_);
v_i_boxed_791_ = lean_unbox_usize(v_i_788_);
lean_dec(v_i_788_);
v_res_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_boxed_790_, v_i_boxed_791_, v_bs_789_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(size_t v_sz_793_, size_t v_i_794_, lean_object* v_bs_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_lt(v_i_794_, v_sz_793_);
if (v___x_796_ == 0)
{
return v_bs_795_;
}
else
{
lean_object* v_v_797_; lean_object* v_snd_798_; lean_object* v___x_799_; lean_object* v_bs_x27_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_v_797_ = lean_array_uget_borrowed(v_bs_795_, v_i_794_);
v_snd_798_ = lean_ctor_get(v_v_797_, 1);
lean_inc(v_snd_798_);
v___x_799_ = lean_unsigned_to_nat(0u);
v_bs_x27_800_ = lean_array_uset(v_bs_795_, v_i_794_, v___x_799_);
v___x_801_ = ((size_t)1ULL);
v___x_802_ = lean_usize_add(v_i_794_, v___x_801_);
v___x_803_ = lean_array_uset(v_bs_x27_800_, v_i_794_, v_snd_798_);
v_i_794_ = v___x_802_;
v_bs_795_ = v___x_803_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1___boxed(lean_object* v_sz_805_, lean_object* v_i_806_, lean_object* v_bs_807_){
_start:
{
size_t v_sz_boxed_808_; size_t v_i_boxed_809_; lean_object* v_res_810_; 
v_sz_boxed_808_ = lean_unbox_usize(v_sz_805_);
lean_dec(v_sz_805_);
v_i_boxed_809_ = lean_unbox_usize(v_i_806_);
lean_dec(v_i_806_);
v_res_810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_boxed_808_, v_i_boxed_809_, v_bs_807_);
return v_res_810_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__14));
v___x_828_ = l_String_toRawSubstring_x27(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__18));
v___x_834_ = l_String_toRawSubstring_x27(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__27));
v___x_845_ = l_String_toRawSubstring_x27(v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(lean_object* v_x_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_868_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__1));
lean_inc(v_x_864_);
v___x_869_ = l_Lean_Syntax_isOfKind(v_x_864_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_dec(v_x_864_);
v___x_870_ = lean_box(1);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v_a_866_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; lean_object* v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; size_t v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_946_; lean_object* v___y_947_; lean_object* v___y_948_; lean_object* v___y_949_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v___y_954_; size_t v___y_955_; lean_object* v___y_956_; lean_object* v___y_957_; lean_object* v___y_958_; lean_object* v___y_959_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; lean_object* v___y_1014_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; size_t v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1023_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; size_t v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; size_t v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; size_t v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; size_t v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v_doc_x3f_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_1408_ = l_Lean_Syntax_getArg(v_x_864_, v___x_872_);
v___x_1409_ = l_Lean_Syntax_isNone(v___x_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; uint8_t v___x_1411_; 
v___x_1410_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_1408_);
v___x_1411_ = l_Lean_Syntax_matchesNull(v___x_1408_, v___x_1410_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_dec(v___x_1408_);
lean_dec(v_x_864_);
v___x_1412_ = lean_box(1);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
lean_ctor_set(v___x_1413_, 1, v_a_866_);
return v___x_1413_;
}
else
{
lean_object* v_doc_x3f_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_doc_x3f_1414_ = l_Lean_Syntax_getArg(v___x_1408_, v___x_872_);
lean_dec(v___x_1408_);
v___x_1415_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__36));
lean_inc(v_doc_x3f_1414_);
v___x_1416_ = l_Lean_Syntax_isOfKind(v_doc_x3f_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec(v_doc_x3f_1414_);
lean_dec(v_x_864_);
v___x_1417_ = lean_box(1);
v___x_1418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_a_866_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_doc_x3f_1414_);
v_doc_x3f_1361_ = v___x_1419_;
v___y_1362_ = v_a_865_;
v___y_1363_ = v_a_866_;
goto v___jp_1360_;
}
}
}
else
{
lean_object* v___x_1420_; 
lean_dec(v___x_1408_);
v___x_1420_ = lean_box(0);
v_doc_x3f_1361_ = v___x_1420_;
v___y_1362_ = v_a_865_;
v___y_1363_ = v_a_866_;
goto v___jp_1360_;
}
v___jp_873_:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; size_t v_sz_902_; lean_object* v___x_903_; size_t v_sz_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_892_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_893_ = lean_box(2);
lean_inc_n(v___y_887_, 4);
v___x_894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
lean_ctor_set(v___x_894_, 1, v___y_887_);
lean_ctor_set(v___x_894_, 2, v___x_892_);
v___x_895_ = lean_mk_empty_array_with_capacity(v___y_882_);
v___x_896_ = lean_array_push(v___x_895_, v___y_891_);
v___x_897_ = lean_array_push(v___x_896_, v___x_894_);
v___x_898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_898_, 0, v___x_893_);
lean_ctor_set(v___x_898_, 1, v___y_881_);
lean_ctor_set(v___x_898_, 2, v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_888_);
lean_inc_ref_n(v___y_879_, 6);
v___x_900_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___y_888_, v___x_899_);
v___x_901_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_902_ = lean_array_size(v___y_878_);
v___x_903_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_902_, v___y_889_, v___y_878_);
v_sz_904_ = lean_array_size(v___x_903_);
v___x_905_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_904_, v___y_889_, v___x_903_);
lean_inc_ref(v___y_885_);
v___x_906_ = l_Array_append___redArg(v___y_885_, v___x_905_);
lean_dec_ref(v___x_905_);
lean_inc_n(v___y_875_, 14);
v___x_907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_907_, 0, v___y_875_);
lean_ctor_set(v___x_907_, 1, v___y_887_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_877_, 2);
v___x_909_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___y_877_, v___x_908_);
v___x_910_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_911_, 0, v___y_875_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_913_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___y_877_, v___x_912_);
v___x_914_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_915_, 0, v___y_875_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_917_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___x_916_, v___x_901_);
v___x_918_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_919_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_919_, 0, v___y_875_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_Syntax_node1(v___y_875_, v___x_917_, v___x_919_);
v___x_921_ = l_Lean_Syntax_node1(v___y_875_, v___y_887_, v___x_920_);
v___x_922_ = l_Lean_Syntax_node2(v___y_875_, v___x_913_, v___x_915_, v___x_921_);
v___x_923_ = l_Lean_Syntax_node2(v___y_875_, v___x_909_, v___x_911_, v___x_922_);
v___x_924_ = l_Lean_Syntax_node1(v___y_875_, v___y_887_, v___x_923_);
v___x_925_ = l_Lean_Syntax_node2(v___y_875_, v___x_900_, v___x_907_, v___x_924_);
v___x_926_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_927_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___y_888_, v___x_926_);
v___x_928_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_929_, 0, v___y_875_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_931_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_932_ = l_Lean_Name_mkStr4(v___x_867_, v___y_879_, v___x_930_, v___x_931_);
lean_inc_n(v___y_884_, 3);
v___x_933_ = l_Lean_Syntax_node2(v___y_875_, v___x_932_, v___y_884_, v___y_884_);
v___x_934_ = l_Lean_Syntax_node4(v___y_875_, v___x_927_, v___x_929_, v___y_890_, v___x_933_, v___y_884_);
v___x_935_ = l_Lean_Syntax_node5(v___y_875_, v___y_883_, v___y_880_, v___x_898_, v___x_925_, v___x_934_, v___y_884_);
v___x_936_ = l_Lean_Syntax_node2(v___y_875_, v___y_876_, v___y_886_, v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___y_874_);
return v___x_937_;
}
v___jp_938_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_inc_ref_n(v___y_952_, 2);
v___x_960_ = l_Array_append___redArg(v___y_952_, v___y_959_);
lean_dec_ref(v___y_959_);
lean_inc_n(v___y_953_, 5);
lean_inc_n(v___y_941_, 20);
v___x_961_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_961_, 0, v___y_941_);
lean_ctor_set(v___x_961_, 1, v___y_953_);
lean_ctor_set(v___x_961_, 2, v___x_960_);
v___x_962_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_944_, 2);
lean_inc_ref_n(v___y_948_, 6);
v___x_963_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___y_944_, v___x_962_);
v___x_964_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_965_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_965_, 0, v___y_941_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_967_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___y_944_, v___x_966_);
v___x_968_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_969_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_970_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___x_968_, v___x_969_);
v___x_971_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_972_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_951_);
lean_inc(v___y_947_);
v___x_973_ = l_Lean_addMacroScope(v___y_947_, v___x_972_, v___y_951_);
lean_inc_n(v___y_940_, 2);
v___x_974_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_974_, 0, v___y_941_);
lean_ctor_set(v___x_974_, 1, v___x_971_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v___y_940_);
v___x_975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_975_, 0, v___y_941_);
lean_ctor_set(v___x_975_, 1, v___y_953_);
lean_ctor_set(v___x_975_, 2, v___y_952_);
lean_inc_ref_n(v___x_975_, 7);
lean_inc(v___x_970_);
v___x_976_ = l_Lean_Syntax_node2(v___y_941_, v___x_970_, v___x_974_, v___x_975_);
lean_inc(v___x_967_);
v___x_977_ = l_Lean_Syntax_node2(v___y_941_, v___x_967_, v___y_945_, v___x_976_);
v___x_978_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_979_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_941_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
lean_inc(v___y_956_);
v___x_980_ = l_Lean_Syntax_node1(v___y_941_, v___y_956_, v___x_975_);
v___x_981_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_982_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_983_ = l_Lean_addMacroScope(v___y_947_, v___x_982_, v___y_951_);
v___x_984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_984_, 0, v___y_941_);
lean_ctor_set(v___x_984_, 1, v___x_981_);
lean_ctor_set(v___x_984_, 2, v___x_983_);
lean_ctor_set(v___x_984_, 3, v___y_940_);
v___x_985_ = l_Lean_Syntax_node2(v___y_941_, v___x_970_, v___x_984_, v___x_975_);
v___x_986_ = l_Lean_Syntax_node2(v___y_941_, v___x_967_, v___x_980_, v___x_985_);
v___x_987_ = l_Lean_Syntax_node3(v___y_941_, v___y_953_, v___x_977_, v___x_979_, v___x_986_);
v___x_988_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_989_, 0, v___y_941_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = l_Lean_Syntax_node3(v___y_941_, v___x_963_, v___x_965_, v___x_987_, v___x_989_);
v___x_991_ = l_Lean_Syntax_node1(v___y_941_, v___y_953_, v___x_990_);
v___x_992_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_954_, 3);
v___x_993_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___y_954_, v___x_992_);
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v___y_941_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
v___x_995_ = l_Lean_Syntax_node1(v___y_941_, v___x_993_, v___x_994_);
v___x_996_ = l_Lean_Syntax_node1(v___y_941_, v___y_953_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node7(v___y_941_, v___y_949_, v___x_961_, v___x_991_, v___x_996_, v___x_975_, v___x_975_, v___x_975_, v___x_975_);
v___x_998_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_999_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___y_954_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___y_941_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1003_ = l_Lean_Name_mkStr4(v___x_867_, v___y_948_, v___y_954_, v___x_1002_);
if (lean_obj_tag(v___y_957_) == 0)
{
v___y_874_ = v___y_942_;
v___y_875_ = v___y_941_;
v___y_876_ = v___y_943_;
v___y_877_ = v___y_944_;
v___y_878_ = v___y_946_;
v___y_879_ = v___y_948_;
v___y_880_ = v___x_1001_;
v___y_881_ = v___x_1003_;
v___y_882_ = v___y_950_;
v___y_883_ = v___x_999_;
v___y_884_ = v___x_975_;
v___y_885_ = v___y_952_;
v___y_886_ = v___x_997_;
v___y_887_ = v___y_953_;
v___y_888_ = v___y_954_;
v___y_889_ = v___y_955_;
v___y_890_ = v___y_958_;
v___y_891_ = v___y_939_;
goto v___jp_873_;
}
else
{
lean_object* v_val_1004_; 
lean_dec(v___y_939_);
v_val_1004_ = lean_ctor_get(v___y_957_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v___y_957_, 1);
v___y_874_ = v___y_942_;
v___y_875_ = v___y_941_;
v___y_876_ = v___y_943_;
v___y_877_ = v___y_944_;
v___y_878_ = v___y_946_;
v___y_879_ = v___y_948_;
v___y_880_ = v___x_1001_;
v___y_881_ = v___x_1003_;
v___y_882_ = v___y_950_;
v___y_883_ = v___x_999_;
v___y_884_ = v___x_975_;
v___y_885_ = v___y_952_;
v___y_886_ = v___x_997_;
v___y_887_ = v___y_953_;
v___y_888_ = v___y_954_;
v___y_889_ = v___y_955_;
v___y_890_ = v___y_958_;
v___y_891_ = v_val_1004_;
goto v___jp_873_;
}
}
v___jp_1005_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; size_t v_sz_1034_; lean_object* v___x_1035_; size_t v_sz_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1024_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1025_ = lean_box(2);
lean_inc_n(v___y_1017_, 4);
v___x_1026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___y_1017_);
lean_ctor_set(v___x_1026_, 2, v___x_1024_);
v___x_1027_ = lean_mk_empty_array_with_capacity(v___y_1016_);
v___x_1028_ = lean_array_push(v___x_1027_, v___y_1023_);
v___x_1029_ = lean_array_push(v___x_1028_, v___x_1026_);
v___x_1030_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1025_);
lean_ctor_set(v___x_1030_, 1, v___y_1012_);
lean_ctor_set(v___x_1030_, 2, v___x_1029_);
v___x_1031_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1006_);
lean_inc_ref_n(v___y_1013_, 6);
v___x_1032_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___y_1006_, v___x_1031_);
v___x_1033_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1034_ = lean_array_size(v___y_1011_);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1034_, v___y_1020_, v___y_1011_);
v_sz_1036_ = lean_array_size(v___x_1035_);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1036_, v___y_1020_, v___x_1035_);
lean_inc_ref(v___y_1021_);
v___x_1038_ = l_Array_append___redArg(v___y_1021_, v___x_1037_);
lean_dec_ref(v___x_1037_);
lean_inc_n(v___y_1010_, 14);
v___x_1039_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1039_, 0, v___y_1010_);
lean_ctor_set(v___x_1039_, 1, v___y_1017_);
lean_ctor_set(v___x_1039_, 2, v___x_1038_);
v___x_1040_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1008_, 2);
v___x_1041_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___y_1008_, v___x_1040_);
v___x_1042_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1043_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___y_1010_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1045_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___y_1008_, v___x_1044_);
v___x_1046_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1047_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___y_1010_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1049_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___x_1048_, v___x_1033_);
v___x_1050_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___y_1010_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_Syntax_node1(v___y_1010_, v___x_1049_, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node1(v___y_1010_, v___y_1017_, v___x_1052_);
v___x_1054_ = l_Lean_Syntax_node2(v___y_1010_, v___x_1045_, v___x_1047_, v___x_1053_);
v___x_1055_ = l_Lean_Syntax_node2(v___y_1010_, v___x_1041_, v___x_1043_, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node1(v___y_1010_, v___y_1017_, v___x_1055_);
v___x_1057_ = l_Lean_Syntax_node2(v___y_1010_, v___x_1032_, v___x_1039_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1059_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___y_1006_, v___x_1058_);
v___x_1060_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1061_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___y_1010_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1063_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1064_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1013_, v___x_1062_, v___x_1063_);
lean_inc_n(v___y_1014_, 3);
v___x_1065_ = l_Lean_Syntax_node2(v___y_1010_, v___x_1064_, v___y_1014_, v___y_1014_);
v___x_1066_ = l_Lean_Syntax_node4(v___y_1010_, v___x_1059_, v___x_1061_, v___y_1022_, v___x_1065_, v___y_1014_);
v___x_1067_ = l_Lean_Syntax_node5(v___y_1010_, v___y_1015_, v___y_1018_, v___x_1030_, v___x_1057_, v___x_1066_, v___y_1014_);
v___x_1068_ = l_Lean_Syntax_node2(v___y_1010_, v___y_1007_, v___y_1009_, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___y_1019_);
return v___x_1069_;
}
v___jp_1070_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc_ref_n(v___y_1087_, 2);
v___x_1092_ = l_Array_append___redArg(v___y_1087_, v___y_1091_);
lean_dec_ref(v___y_1091_);
lean_inc_n(v___y_1084_, 5);
lean_inc_n(v___y_1076_, 20);
v___x_1093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___y_1076_);
lean_ctor_set(v___x_1093_, 1, v___y_1084_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1075_, 2);
lean_inc_ref_n(v___y_1080_, 6);
v___x_1095_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___y_1075_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___y_1076_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1099_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___y_1075_, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1101_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1102_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___x_1100_, v___x_1101_);
v___x_1103_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1104_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
lean_inc(v___y_1082_);
lean_inc(v___y_1079_);
v___x_1105_ = l_Lean_addMacroScope(v___y_1079_, v___x_1104_, v___y_1082_);
lean_inc_n(v___y_1072_, 2);
v___x_1106_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1106_, 0, v___y_1076_);
lean_ctor_set(v___x_1106_, 1, v___x_1103_);
lean_ctor_set(v___x_1106_, 2, v___x_1105_);
lean_ctor_set(v___x_1106_, 3, v___y_1072_);
v___x_1107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1076_);
lean_ctor_set(v___x_1107_, 1, v___y_1084_);
lean_ctor_set(v___x_1107_, 2, v___y_1087_);
lean_inc_ref_n(v___x_1107_, 7);
lean_inc(v___x_1102_);
v___x_1108_ = l_Lean_Syntax_node2(v___y_1076_, v___x_1102_, v___x_1106_, v___x_1107_);
lean_inc(v___x_1099_);
v___x_1109_ = l_Lean_Syntax_node2(v___y_1076_, v___x_1099_, v___y_1077_, v___x_1108_);
v___x_1110_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1111_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___y_1076_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_inc(v___y_1088_);
v___x_1112_ = l_Lean_Syntax_node1(v___y_1076_, v___y_1088_, v___x_1107_);
v___x_1113_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__19);
v___x_1114_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__20));
v___x_1115_ = l_Lean_addMacroScope(v___y_1079_, v___x_1114_, v___y_1082_);
v___x_1116_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1116_, 0, v___y_1076_);
lean_ctor_set(v___x_1116_, 1, v___x_1113_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
lean_ctor_set(v___x_1116_, 3, v___y_1072_);
v___x_1117_ = l_Lean_Syntax_node2(v___y_1076_, v___x_1102_, v___x_1116_, v___x_1107_);
v___x_1118_ = l_Lean_Syntax_node2(v___y_1076_, v___x_1099_, v___x_1112_, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node3(v___y_1076_, v___y_1084_, v___x_1109_, v___x_1111_, v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___y_1076_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_Syntax_node3(v___y_1076_, v___x_1095_, v___x_1097_, v___x_1119_, v___x_1121_);
v___x_1123_ = l_Lean_Syntax_node1(v___y_1076_, v___y_1084_, v___x_1122_);
v___x_1124_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__22));
lean_inc_ref_n(v___y_1073_, 3);
v___x_1125_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___y_1073_, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___y_1076_);
lean_ctor_set(v___x_1126_, 1, v___x_1124_);
v___x_1127_ = l_Lean_Syntax_node1(v___y_1076_, v___x_1125_, v___x_1126_);
v___x_1128_ = l_Lean_Syntax_node1(v___y_1076_, v___y_1084_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node7(v___y_1076_, v___y_1083_, v___x_1093_, v___x_1123_, v___x_1128_, v___x_1107_, v___x_1107_, v___x_1107_, v___x_1107_);
v___x_1130_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1131_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___y_1073_, v___x_1130_);
v___x_1132_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___y_1076_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1135_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1080_, v___y_1073_, v___x_1134_);
if (lean_obj_tag(v___y_1089_) == 0)
{
v___y_1006_ = v___y_1073_;
v___y_1007_ = v___y_1074_;
v___y_1008_ = v___y_1075_;
v___y_1009_ = v___x_1129_;
v___y_1010_ = v___y_1076_;
v___y_1011_ = v___y_1078_;
v___y_1012_ = v___x_1135_;
v___y_1013_ = v___y_1080_;
v___y_1014_ = v___x_1107_;
v___y_1015_ = v___x_1131_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___y_1084_;
v___y_1018_ = v___x_1133_;
v___y_1019_ = v___y_1085_;
v___y_1020_ = v___y_1086_;
v___y_1021_ = v___y_1087_;
v___y_1022_ = v___y_1090_;
v___y_1023_ = v___y_1071_;
goto v___jp_1005_;
}
else
{
lean_object* v_val_1136_; 
lean_dec(v___y_1071_);
v_val_1136_ = lean_ctor_get(v___y_1089_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v___y_1089_, 1);
v___y_1006_ = v___y_1073_;
v___y_1007_ = v___y_1074_;
v___y_1008_ = v___y_1075_;
v___y_1009_ = v___x_1129_;
v___y_1010_ = v___y_1076_;
v___y_1011_ = v___y_1078_;
v___y_1012_ = v___x_1135_;
v___y_1013_ = v___y_1080_;
v___y_1014_ = v___x_1107_;
v___y_1015_ = v___x_1131_;
v___y_1016_ = v___y_1081_;
v___y_1017_ = v___y_1084_;
v___y_1018_ = v___x_1133_;
v___y_1019_ = v___y_1085_;
v___y_1020_ = v___y_1086_;
v___y_1021_ = v___y_1087_;
v___y_1022_ = v___y_1090_;
v___y_1023_ = v_val_1136_;
goto v___jp_1005_;
}
}
v___jp_1137_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; size_t v_sz_1166_; lean_object* v___x_1167_; size_t v_sz_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1156_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__0));
v___x_1157_ = lean_box(2);
lean_inc_n(v___y_1138_, 4);
v___x_1158_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1157_);
lean_ctor_set(v___x_1158_, 1, v___y_1138_);
lean_ctor_set(v___x_1158_, 2, v___x_1156_);
v___x_1159_ = lean_mk_empty_array_with_capacity(v___y_1145_);
v___x_1160_ = lean_array_push(v___x_1159_, v___y_1155_);
v___x_1161_ = lean_array_push(v___x_1160_, v___x_1158_);
v___x_1162_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1157_);
lean_ctor_set(v___x_1162_, 1, v___y_1152_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
v___x_1163_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__1));
lean_inc_ref(v___y_1143_);
lean_inc_ref_n(v___y_1144_, 6);
v___x_1164_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___y_1143_, v___x_1163_);
v___x_1165_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__10));
v_sz_1166_ = lean_array_size(v___y_1141_);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_1166_, v___y_1150_, v___y_1141_);
v_sz_1168_ = lean_array_size(v___x_1167_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_1168_, v___y_1150_, v___x_1167_);
lean_inc_ref(v___y_1153_);
v___x_1170_ = l_Array_append___redArg(v___y_1153_, v___x_1169_);
lean_dec_ref(v___x_1169_);
lean_inc_n(v___y_1151_, 14);
v___x_1171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1171_, 0, v___y_1151_);
lean_ctor_set(v___x_1171_, 1, v___y_1138_);
lean_ctor_set(v___x_1171_, 2, v___x_1170_);
v___x_1172_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref_n(v___y_1139_, 2);
v___x_1173_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___y_1139_, v___x_1172_);
v___x_1174_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_1175_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___y_1151_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v___x_1176_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__2));
v___x_1177_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___y_1139_, v___x_1176_);
v___x_1178_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__3));
v___x_1179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___y_1151_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
v___x_1180_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__4));
v___x_1181_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___x_1180_, v___x_1165_);
v___x_1182_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_1183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___y_1151_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_Syntax_node1(v___y_1151_, v___x_1181_, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_node1(v___y_1151_, v___y_1138_, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node2(v___y_1151_, v___x_1177_, v___x_1179_, v___x_1185_);
v___x_1187_ = l_Lean_Syntax_node2(v___y_1151_, v___x_1173_, v___x_1175_, v___x_1186_);
v___x_1188_ = l_Lean_Syntax_node1(v___y_1151_, v___y_1138_, v___x_1187_);
v___x_1189_ = l_Lean_Syntax_node2(v___y_1151_, v___x_1164_, v___x_1171_, v___x_1188_);
v___x_1190_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__5));
v___x_1191_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___y_1143_, v___x_1190_);
v___x_1192_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_1193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___y_1151_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__7));
v___x_1195_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__8));
v___x_1196_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1144_, v___x_1194_, v___x_1195_);
lean_inc_n(v___y_1149_, 3);
v___x_1197_ = l_Lean_Syntax_node2(v___y_1151_, v___x_1196_, v___y_1149_, v___y_1149_);
v___x_1198_ = l_Lean_Syntax_node4(v___y_1151_, v___x_1191_, v___x_1193_, v___y_1154_, v___x_1197_, v___y_1149_);
v___x_1199_ = l_Lean_Syntax_node5(v___y_1151_, v___y_1142_, v___y_1140_, v___x_1162_, v___x_1189_, v___x_1198_, v___y_1149_);
v___x_1200_ = l_Lean_Syntax_node2(v___y_1151_, v___y_1146_, v___y_1147_, v___x_1199_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
lean_ctor_set(v___x_1201_, 1, v___y_1148_);
return v___x_1201_;
}
v___jp_1202_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc_ref_n(v___y_1219_, 2);
v___x_1223_ = l_Array_append___redArg(v___y_1219_, v___y_1222_);
lean_dec_ref(v___y_1222_);
lean_inc_n(v___y_1204_, 5);
lean_inc_n(v___y_1218_, 15);
v___x_1224_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1224_, 0, v___y_1218_);
lean_ctor_set(v___x_1224_, 1, v___y_1204_);
lean_ctor_set(v___x_1224_, 2, v___x_1223_);
v___x_1225_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__9));
lean_inc_ref_n(v___y_1206_, 2);
lean_inc_ref_n(v___y_1212_, 6);
v___x_1226_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___y_1206_, v___x_1225_);
v___x_1227_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__10));
v___x_1228_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1228_, 0, v___y_1218_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
v___x_1230_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___y_1206_, v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__12));
v___x_1232_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__13));
v___x_1233_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___x_1231_, v___x_1232_);
v___x_1234_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__15);
v___x_1235_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__16));
v___x_1236_ = l_Lean_addMacroScope(v___y_1209_, v___x_1235_, v___y_1215_);
lean_inc(v___y_1205_);
v___x_1237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1237_, 0, v___y_1218_);
lean_ctor_set(v___x_1237_, 1, v___x_1234_);
lean_ctor_set(v___x_1237_, 2, v___x_1236_);
lean_ctor_set(v___x_1237_, 3, v___y_1205_);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v___y_1218_);
lean_ctor_set(v___x_1238_, 1, v___y_1204_);
lean_ctor_set(v___x_1238_, 2, v___y_1219_);
lean_inc_ref_n(v___x_1238_, 5);
v___x_1239_ = l_Lean_Syntax_node2(v___y_1218_, v___x_1233_, v___x_1237_, v___x_1238_);
v___x_1240_ = l_Lean_Syntax_node2(v___y_1218_, v___x_1230_, v___y_1207_, v___x_1239_);
v___x_1241_ = l_Lean_Syntax_node1(v___y_1218_, v___y_1204_, v___x_1240_);
v___x_1242_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___y_1218_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
v___x_1244_ = l_Lean_Syntax_node3(v___y_1218_, v___x_1226_, v___x_1228_, v___x_1241_, v___x_1243_);
v___x_1245_ = l_Lean_Syntax_node1(v___y_1218_, v___y_1204_, v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__26));
lean_inc_ref_n(v___y_1210_, 3);
v___x_1247_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___y_1210_, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___y_1218_);
lean_ctor_set(v___x_1248_, 1, v___x_1246_);
v___x_1249_ = l_Lean_Syntax_node1(v___y_1218_, v___x_1247_, v___x_1248_);
v___x_1250_ = l_Lean_Syntax_node1(v___y_1218_, v___y_1204_, v___x_1249_);
v___x_1251_ = l_Lean_Syntax_node7(v___y_1218_, v___y_1211_, v___x_1224_, v___x_1245_, v___x_1250_, v___x_1238_, v___x_1238_, v___x_1238_, v___x_1238_);
v___x_1252_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__23));
v___x_1253_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___y_1210_, v___x_1252_);
v___x_1254_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__24));
v___x_1255_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1255_, 0, v___y_1218_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
v___x_1256_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__25));
v___x_1257_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1212_, v___y_1210_, v___x_1256_);
if (lean_obj_tag(v___y_1220_) == 0)
{
v___y_1138_ = v___y_1204_;
v___y_1139_ = v___y_1206_;
v___y_1140_ = v___x_1255_;
v___y_1141_ = v___y_1208_;
v___y_1142_ = v___x_1253_;
v___y_1143_ = v___y_1210_;
v___y_1144_ = v___y_1212_;
v___y_1145_ = v___y_1213_;
v___y_1146_ = v___y_1214_;
v___y_1147_ = v___x_1251_;
v___y_1148_ = v___y_1216_;
v___y_1149_ = v___x_1238_;
v___y_1150_ = v___y_1217_;
v___y_1151_ = v___y_1218_;
v___y_1152_ = v___x_1257_;
v___y_1153_ = v___y_1219_;
v___y_1154_ = v___y_1221_;
v___y_1155_ = v___y_1203_;
goto v___jp_1137_;
}
else
{
lean_object* v_val_1258_; 
lean_dec(v___y_1203_);
v_val_1258_ = lean_ctor_get(v___y_1220_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v___y_1220_, 1);
v___y_1138_ = v___y_1204_;
v___y_1139_ = v___y_1206_;
v___y_1140_ = v___x_1255_;
v___y_1141_ = v___y_1208_;
v___y_1142_ = v___x_1253_;
v___y_1143_ = v___y_1210_;
v___y_1144_ = v___y_1212_;
v___y_1145_ = v___y_1213_;
v___y_1146_ = v___y_1214_;
v___y_1147_ = v___x_1251_;
v___y_1148_ = v___y_1216_;
v___y_1149_ = v___x_1238_;
v___y_1150_ = v___y_1217_;
v___y_1151_ = v___y_1218_;
v___y_1152_ = v___x_1257_;
v___y_1153_ = v___y_1219_;
v___y_1154_ = v___y_1221_;
v___y_1155_ = v_val_1258_;
goto v___jp_1137_;
}
}
v___jp_1259_:
{
lean_object* v_quotContext_1276_; lean_object* v_currMacroScope_1277_; lean_object* v_ref_1278_; lean_object* v___x_1279_; lean_object* v_a_1280_; lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1359_; 
v_quotContext_1276_ = lean_ctor_get(v___y_1271_, 1);
v_currMacroScope_1277_ = lean_ctor_get(v___y_1271_, 2);
v_ref_1278_ = lean_ctor_get(v___y_1271_, 5);
v___x_1279_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1278_, v___y_1271_, v___y_1270_);
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_a_1281_ = lean_ctor_get(v___x_1279_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1283_ = v___x_1279_;
v_isShared_1284_ = v_isSharedCheck_1359_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1359_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1285_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__3));
v___x_1286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3___closed__4));
lean_inc(v_a_1280_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 2);
lean_ctor_set(v___x_1283_, 1, v___x_1286_);
v___x_1288_ = v___x_1283_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1280_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1286_);
v___x_1288_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; size_t v_sz_1292_; lean_object* v___x_1293_; 
v___x_1289_ = l_Lean_Syntax_node3(v_a_1280_, v___x_1285_, v___y_1264_, v___x_1288_, v___y_1267_);
v___x_1290_ = l_Array_zip___redArg(v___y_1268_, v___y_1274_);
lean_dec_ref(v___y_1274_);
lean_dec_ref(v___y_1268_);
v___x_1291_ = l_Array_reverse___redArg(v___x_1290_);
v_sz_1292_ = lean_array_size(v___x_1291_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__3(v___x_1291_, v_sz_1292_, v___y_1272_, v___x_1289_, v___y_1271_, v_a_1281_);
lean_dec_ref(v___x_1291_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v_a_1297_; lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
v_a_1295_ = lean_ctor_get(v___x_1293_, 1);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1293_, 2);
v___x_1296_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1278_, v___y_1271_, v_a_1295_);
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
v_a_1298_ = lean_ctor_get(v___x_1296_, 1);
lean_inc(v_a_1298_);
lean_dec_ref(v___x_1296_);
v___x_1299_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__28);
v___x_1300_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__29));
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___x_1301_ = l_Lean_addMacroScope(v_quotContext_1276_, v___x_1300_, v_currMacroScope_1277_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1303_, 0, v_a_1297_);
lean_ctor_set(v___x_1303_, 1, v___x_1299_);
lean_ctor_set(v___x_1303_, 2, v___x_1301_);
lean_ctor_set(v___x_1303_, 3, v___x_1302_);
v___x_1304_ = l_Lean_Syntax_getArg(v___y_1262_, v___x_872_);
lean_inc(v___x_1304_);
v___x_1305_ = l_Lean_Syntax_matchesNull(v___x_1304_, v___y_1265_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v_a_1307_; lean_object* v_a_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
lean_dec(v___x_1304_);
v___x_1306_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1278_, v___y_1271_, v_a_1298_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
v_a_1308_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_a_1308_);
lean_dec_ref(v___x_1306_);
v___x_1309_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1310_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1266_, 2);
v___x_1311_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1309_, v___x_1310_);
v___x_1312_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1313_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1309_, v___x_1312_);
v___x_1314_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1315_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1260_) == 1)
{
lean_object* v_val_1316_; lean_object* v___x_1317_; 
v_val_1316_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_val_1316_);
lean_dec_ref_known(v___y_1260_, 1);
v___x_1317_ = l_Array_mkArray1___redArg(v_val_1316_);
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_939_ = v___x_1303_;
v___y_940_ = v___x_1302_;
v___y_941_ = v_a_1307_;
v___y_942_ = v_a_1308_;
v___y_943_ = v___x_1311_;
v___y_944_ = v___y_1261_;
v___y_945_ = v___y_1262_;
v___y_946_ = v___y_1263_;
v___y_947_ = v_quotContext_1276_;
v___y_948_ = v___y_1266_;
v___y_949_ = v___x_1313_;
v___y_950_ = v___y_1269_;
v___y_951_ = v_currMacroScope_1277_;
v___y_952_ = v___x_1315_;
v___y_953_ = v___x_1314_;
v___y_954_ = v___x_1309_;
v___y_955_ = v___y_1272_;
v___y_956_ = v___y_1273_;
v___y_957_ = v___y_1275_;
v___y_958_ = v_a_1294_;
v___y_959_ = v___x_1317_;
goto v___jp_938_;
}
else
{
lean_object* v___x_1318_; 
lean_dec(v___y_1260_);
v___x_1318_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_939_ = v___x_1303_;
v___y_940_ = v___x_1302_;
v___y_941_ = v_a_1307_;
v___y_942_ = v_a_1308_;
v___y_943_ = v___x_1311_;
v___y_944_ = v___y_1261_;
v___y_945_ = v___y_1262_;
v___y_946_ = v___y_1263_;
v___y_947_ = v_quotContext_1276_;
v___y_948_ = v___y_1266_;
v___y_949_ = v___x_1313_;
v___y_950_ = v___y_1269_;
v___y_951_ = v_currMacroScope_1277_;
v___y_952_ = v___x_1315_;
v___y_953_ = v___x_1314_;
v___y_954_ = v___x_1309_;
v___y_955_ = v___y_1272_;
v___y_956_ = v___y_1273_;
v___y_957_ = v___y_1275_;
v___y_958_ = v_a_1294_;
v___y_959_ = v___x_1318_;
goto v___jp_938_;
}
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1319_ = l_Lean_Syntax_getArg(v___x_1304_, v___x_872_);
lean_dec(v___x_1304_);
v___x_1320_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__34));
lean_inc_ref(v___y_1261_);
lean_inc_ref(v___y_1266_);
v___x_1321_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___y_1261_, v___x_1320_);
v___x_1322_ = l_Lean_Syntax_isOfKind(v___x_1319_, v___x_1321_);
lean_dec(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1323_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1278_, v___y_1271_, v_a_1298_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
v_a_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_a_1325_);
lean_dec_ref(v___x_1323_);
v___x_1326_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1327_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1266_, 2);
v___x_1328_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1326_, v___x_1327_);
v___x_1329_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1330_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1326_, v___x_1329_);
v___x_1331_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1332_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1260_) == 1)
{
lean_object* v_val_1333_; lean_object* v___x_1334_; 
v_val_1333_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_val_1333_);
lean_dec_ref_known(v___y_1260_, 1);
v___x_1334_ = l_Array_mkArray1___redArg(v_val_1333_);
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_1071_ = v___x_1303_;
v___y_1072_ = v___x_1302_;
v___y_1073_ = v___x_1326_;
v___y_1074_ = v___x_1328_;
v___y_1075_ = v___y_1261_;
v___y_1076_ = v_a_1324_;
v___y_1077_ = v___y_1262_;
v___y_1078_ = v___y_1263_;
v___y_1079_ = v_quotContext_1276_;
v___y_1080_ = v___y_1266_;
v___y_1081_ = v___y_1269_;
v___y_1082_ = v_currMacroScope_1277_;
v___y_1083_ = v___x_1330_;
v___y_1084_ = v___x_1331_;
v___y_1085_ = v_a_1325_;
v___y_1086_ = v___y_1272_;
v___y_1087_ = v___x_1332_;
v___y_1088_ = v___y_1273_;
v___y_1089_ = v___y_1275_;
v___y_1090_ = v_a_1294_;
v___y_1091_ = v___x_1334_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1335_; 
lean_dec(v___y_1260_);
v___x_1335_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_1071_ = v___x_1303_;
v___y_1072_ = v___x_1302_;
v___y_1073_ = v___x_1326_;
v___y_1074_ = v___x_1328_;
v___y_1075_ = v___y_1261_;
v___y_1076_ = v_a_1324_;
v___y_1077_ = v___y_1262_;
v___y_1078_ = v___y_1263_;
v___y_1079_ = v_quotContext_1276_;
v___y_1080_ = v___y_1266_;
v___y_1081_ = v___y_1269_;
v___y_1082_ = v_currMacroScope_1277_;
v___y_1083_ = v___x_1330_;
v___y_1084_ = v___x_1331_;
v___y_1085_ = v_a_1325_;
v___y_1086_ = v___y_1272_;
v___y_1087_ = v___x_1332_;
v___y_1088_ = v___y_1273_;
v___y_1089_ = v___y_1275_;
v___y_1090_ = v_a_1294_;
v___y_1091_ = v___x_1335_;
goto v___jp_1070_;
}
}
else
{
lean_object* v___x_1336_; lean_object* v_a_1337_; lean_object* v_a_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1336_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___lam__0(v_ref_1278_, v___y_1271_, v_a_1298_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
v_a_1338_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_a_1338_);
lean_dec_ref(v___x_1336_);
v___x_1339_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__30));
v___x_1340_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__31));
lean_inc_ref_n(v___y_1266_, 2);
v___x_1341_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1339_, v___x_1340_);
v___x_1342_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__32));
v___x_1343_ = l_Lean_Name_mkStr4(v___x_867_, v___y_1266_, v___x_1339_, v___x_1342_);
v___x_1344_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1345_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
if (lean_obj_tag(v___y_1260_) == 1)
{
lean_object* v_val_1346_; lean_object* v___x_1347_; 
v_val_1346_ = lean_ctor_get(v___y_1260_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___y_1260_, 1);
v___x_1347_ = l_Array_mkArray1___redArg(v_val_1346_);
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_1203_ = v___x_1303_;
v___y_1204_ = v___x_1344_;
v___y_1205_ = v___x_1302_;
v___y_1206_ = v___y_1261_;
v___y_1207_ = v___y_1262_;
v___y_1208_ = v___y_1263_;
v___y_1209_ = v_quotContext_1276_;
v___y_1210_ = v___x_1339_;
v___y_1211_ = v___x_1343_;
v___y_1212_ = v___y_1266_;
v___y_1213_ = v___y_1269_;
v___y_1214_ = v___x_1341_;
v___y_1215_ = v_currMacroScope_1277_;
v___y_1216_ = v_a_1338_;
v___y_1217_ = v___y_1272_;
v___y_1218_ = v_a_1337_;
v___y_1219_ = v___x_1345_;
v___y_1220_ = v___y_1275_;
v___y_1221_ = v_a_1294_;
v___y_1222_ = v___x_1347_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1348_; 
lean_dec(v___y_1260_);
v___x_1348_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
lean_inc(v_currMacroScope_1277_);
lean_inc(v_quotContext_1276_);
v___y_1203_ = v___x_1303_;
v___y_1204_ = v___x_1344_;
v___y_1205_ = v___x_1302_;
v___y_1206_ = v___y_1261_;
v___y_1207_ = v___y_1262_;
v___y_1208_ = v___y_1263_;
v___y_1209_ = v_quotContext_1276_;
v___y_1210_ = v___x_1339_;
v___y_1211_ = v___x_1343_;
v___y_1212_ = v___y_1266_;
v___y_1213_ = v___y_1269_;
v___y_1214_ = v___x_1341_;
v___y_1215_ = v_currMacroScope_1277_;
v___y_1216_ = v_a_1338_;
v___y_1217_ = v___y_1272_;
v___y_1218_ = v_a_1337_;
v___y_1219_ = v___x_1345_;
v___y_1220_ = v___y_1275_;
v___y_1221_ = v_a_1294_;
v___y_1222_ = v___x_1348_;
goto v___jp_1202_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec(v___y_1260_);
v_a_1349_ = lean_ctor_get(v___x_1293_, 0);
v_a_1350_ = lean_ctor_get(v___x_1293_, 1);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1293_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_inc(v_a_1349_);
lean_dec(v___x_1293_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1349_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
v___jp_1360_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1364_ = lean_unsigned_to_nat(1u);
v___x_1365_ = l_Lean_Syntax_getArg(v_x_864_, v___x_1364_);
v___x_1366_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_1367_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v___x_1368_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__35));
lean_inc(v___x_1365_);
v___x_1369_ = l_Lean_Syntax_isOfKind(v___x_1365_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec(v___x_1365_);
lean_dec(v_doc_x3f_1361_);
lean_dec(v_x_864_);
v___x_1370_ = lean_box(1);
v___x_1371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
lean_ctor_set(v___x_1371_, 1, v___y_1363_);
return v___x_1371_;
}
else
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1372_ = lean_unsigned_to_nat(6u);
v___x_1373_ = l_Lean_Syntax_getArg(v_x_864_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_getArgs(v___x_1373_);
lean_dec(v___x_1373_);
v_sz_1375_ = lean_array_size(v___x_1374_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__0(v_sz_1375_, v___x_1376_, v___x_1374_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v___x_1365_);
lean_dec(v_doc_x3f_1361_);
lean_dec(v_x_864_);
v___x_1378_ = lean_box(1);
v___x_1379_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___y_1363_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; uint8_t v___x_1384_; 
v_val_1380_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v___x_1377_, 1);
v___x_1381_ = lean_unsigned_to_nat(8u);
v___x_1382_ = l_Lean_Syntax_getArg(v_x_864_, v___x_1381_);
v___x_1383_ = ((lean_object*)(l_Lean_unifConstraint___closed__1));
lean_inc(v___x_1382_);
v___x_1384_ = l_Lean_Syntax_isOfKind(v___x_1382_, v___x_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec(v___x_1382_);
lean_dec(v_val_1380_);
lean_dec(v___x_1365_);
lean_dec(v_doc_x3f_1361_);
lean_dec(v_x_864_);
v___x_1385_ = lean_box(1);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___y_1363_);
return v___x_1386_;
}
else
{
size_t v_sz_1387_; lean_object* v___x_1388_; lean_object* v_cs_u2082_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_cs_u2081_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_bs_1397_; lean_object* v___x_1398_; 
v_sz_1387_ = lean_array_size(v_val_1380_);
v___x_1388_ = lean_unsigned_to_nat(2u);
lean_inc(v_val_1380_);
v_cs_u2082_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__1(v_sz_1387_, v___x_1376_, v_val_1380_);
v___x_1390_ = lean_unsigned_to_nat(3u);
v___x_1391_ = l_Lean_Syntax_getArg(v_x_864_, v___x_1390_);
v___x_1392_ = lean_unsigned_to_nat(4u);
v___x_1393_ = l_Lean_Syntax_getArg(v_x_864_, v___x_1392_);
lean_dec(v_x_864_);
v_cs_u2081_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__2(v_sz_1387_, v___x_1376_, v_val_1380_);
v___x_1395_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_872_);
v___x_1396_ = l_Lean_Syntax_getArg(v___x_1382_, v___x_1388_);
lean_dec(v___x_1382_);
v_bs_1397_ = l_Lean_Syntax_getArgs(v___x_1393_);
lean_dec(v___x_1393_);
v___x_1398_ = l_Lean_Syntax_getOptional_x3f(v___x_1391_);
lean_dec(v___x_1391_);
if (lean_obj_tag(v___x_1398_) == 0)
{
lean_object* v___x_1399_; 
v___x_1399_ = lean_box(0);
v___y_1260_ = v_doc_x3f_1361_;
v___y_1261_ = v___x_1367_;
v___y_1262_ = v___x_1365_;
v___y_1263_ = v_bs_1397_;
v___y_1264_ = v___x_1395_;
v___y_1265_ = v___x_1364_;
v___y_1266_ = v___x_1366_;
v___y_1267_ = v___x_1396_;
v___y_1268_ = v_cs_u2081_1394_;
v___y_1269_ = v___x_1388_;
v___y_1270_ = v___y_1363_;
v___y_1271_ = v___y_1362_;
v___y_1272_ = v___x_1376_;
v___y_1273_ = v___x_1368_;
v___y_1274_ = v_cs_u2082_1389_;
v___y_1275_ = v___x_1399_;
goto v___jp_1259_;
}
else
{
lean_object* v_val_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
v_val_1400_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1398_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_val_1400_);
lean_dec(v___x_1398_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_val_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
v___y_1260_ = v_doc_x3f_1361_;
v___y_1261_ = v___x_1367_;
v___y_1262_ = v___x_1365_;
v___y_1263_ = v_bs_1397_;
v___y_1264_ = v___x_1395_;
v___y_1265_ = v___x_1364_;
v___y_1266_ = v___x_1366_;
v___y_1267_ = v___x_1396_;
v___y_1268_ = v_cs_u2081_1394_;
v___y_1269_ = v___x_1388_;
v___y_1270_ = v___y_1363_;
v___y_1271_ = v___y_1362_;
v___y_1272_ = v___x_1376_;
v___y_1273_ = v___x_1368_;
v___y_1274_ = v_cs_u2082_1389_;
v___y_1275_ = v___x_1405_;
goto v___jp_1259_;
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
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___boxed(lean_object* v_x_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1(v_x_1421_, v_a_1422_, v_a_1423_);
lean_dec_ref(v_a_1422_);
return v_res_1424_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1431_ = l_Lean_explicitBinders;
v___x_1432_ = ((lean_object*)(l_term_u2203___x2c___00__closed__3));
v___x_1433_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1434_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1431_);
return v___x_1434_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1435_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1436_ = lean_obj_once(&l_term_u2203___x2c___00__closed__4, &l_term_u2203___x2c___00__closed__4_once, _init_l_term_u2203___x2c___00__closed__4);
v___x_1437_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1438_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1435_);
return v___x_1438_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1440_ = lean_obj_once(&l_term_u2203___x2c___00__closed__5, &l_term_u2203___x2c___00__closed__5_once, _init_l_term_u2203___x2c___00__closed__5);
v___x_1441_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1442_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v___x_1439_);
return v___x_1442_;
}
}
static lean_object* _init_l_term_u2203___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1443_ = lean_obj_once(&l_term_u2203___x2c___00__closed__6, &l_term_u2203___x2c___00__closed__6_once, _init_l_term_u2203___x2c___00__closed__6);
v___x_1444_ = lean_unsigned_to_nat(1022u);
v___x_1445_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_1446_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
lean_ctor_set(v___x_1446_, 1, v___x_1444_);
lean_ctor_set(v___x_1446_, 2, v___x_1443_);
return v___x_1446_;
}
}
static lean_object* _init_l_term_u2203___x2c__(void){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_obj_once(&l_term_u2203___x2c___00__closed__7, &l_term_u2203___x2c___00__closed__7_once, _init_l_term_u2203___x2c___00__closed__7);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(lean_object* v_x_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v_x_1451_);
v___x_1455_ = l_Lean_Syntax_isOfKind(v_x_1451_, v___x_1454_);
if (v___x_1455_ == 0)
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec(v_x_1451_);
v___x_1456_ = lean_box(1);
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
lean_ctor_set(v___x_1457_, 1, v_a_1453_);
return v___x_1457_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = l_Lean_Syntax_getArg(v_x_1451_, v___x_1458_);
v___x_1460_ = lean_unsigned_to_nat(3u);
v___x_1461_ = l_Lean_Syntax_getArg(v_x_1451_, v___x_1460_);
lean_dec(v_x_1451_);
v___x_1462_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1463_ = l_Lean_expandExplicitBinders(v___x_1462_, v___x_1459_, v___x_1461_, v_a_1452_, v_a_1453_);
lean_dec(v___x_1459_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___boxed(lean_object* v_x_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1(v_x_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1467_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1474_ = l_Lean_explicitBinders;
v___x_1475_ = ((lean_object*)(l_termExists___x2c___00__closed__3));
v___x_1476_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1477_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1477_, 0, v___x_1476_);
lean_ctor_set(v___x_1477_, 1, v___x_1475_);
lean_ctor_set(v___x_1477_, 2, v___x_1474_);
return v___x_1477_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1478_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1479_ = lean_obj_once(&l_termExists___x2c___00__closed__4, &l_termExists___x2c___00__closed__4_once, _init_l_termExists___x2c___00__closed__4);
v___x_1480_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1481_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
lean_ctor_set(v___x_1481_, 2, v___x_1478_);
return v___x_1481_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1482_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1483_ = lean_obj_once(&l_termExists___x2c___00__closed__5, &l_termExists___x2c___00__closed__5_once, _init_l_termExists___x2c___00__closed__5);
v___x_1484_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1485_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
lean_ctor_set(v___x_1485_, 2, v___x_1482_);
return v___x_1485_;
}
}
static lean_object* _init_l_termExists___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1486_ = lean_obj_once(&l_termExists___x2c___00__closed__6, &l_termExists___x2c___00__closed__6_once, _init_l_termExists___x2c___00__closed__6);
v___x_1487_ = lean_unsigned_to_nat(1022u);
v___x_1488_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
v___x_1489_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
lean_ctor_set(v___x_1489_, 1, v___x_1487_);
lean_ctor_set(v___x_1489_, 2, v___x_1486_);
return v___x_1489_;
}
}
static lean_object* _init_l_termExists___x2c__(void){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_termExists___x2c___00__closed__7, &l_termExists___x2c___00__closed__7_once, _init_l_termExists___x2c___00__closed__7);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(lean_object* v_x_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_termExists___x2c___00__closed__1));
lean_inc(v_x_1491_);
v___x_1495_ = l_Lean_Syntax_isOfKind(v_x_1491_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_dec(v_x_1491_);
v___x_1496_ = lean_box(1);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
lean_ctor_set(v___x_1497_, 1, v_a_1493_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = l_Lean_Syntax_getArg(v_x_1491_, v___x_1498_);
v___x_1500_ = lean_unsigned_to_nat(3u);
v___x_1501_ = l_Lean_Syntax_getArg(v_x_1491_, v___x_1500_);
lean_dec(v_x_1491_);
v___x_1502_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u2203___x2c____1___closed__1));
v___x_1503_ = l_Lean_expandExplicitBinders(v___x_1502_, v___x_1499_, v___x_1501_, v_a_1492_, v_a_1493_);
lean_dec(v___x_1499_);
return v___x_1503_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__termExists___x2c____1___boxed(lean_object* v_x_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l___aux__Init__NotationExtra______macroRules__termExists___x2c____1(v_x_1504_, v_a_1505_, v_a_1506_);
lean_dec_ref(v_a_1505_);
return v_res_1507_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = l_Lean_explicitBinders;
v___x_1515_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__3));
v___x_1516_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1517_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1515_);
lean_ctor_set(v___x_1517_, 2, v___x_1514_);
return v___x_1517_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1519_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__4, &l_term_u03a3___x2c___00__closed__4_once, _init_l_term_u03a3___x2c___00__closed__4);
v___x_1520_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1521_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1519_);
lean_ctor_set(v___x_1521_, 2, v___x_1518_);
return v___x_1521_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1522_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1523_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__5, &l_term_u03a3___x2c___00__closed__5_once, _init_l_term_u03a3___x2c___00__closed__5);
v___x_1524_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1525_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1523_);
lean_ctor_set(v___x_1525_, 2, v___x_1522_);
return v___x_1525_;
}
}
static lean_object* _init_l_term_u03a3___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__6, &l_term_u03a3___x2c___00__closed__6_once, _init_l_term_u03a3___x2c___00__closed__6);
v___x_1527_ = lean_unsigned_to_nat(1022u);
v___x_1528_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
v___x_1529_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
lean_ctor_set(v___x_1529_, 1, v___x_1527_);
lean_ctor_set(v___x_1529_, 2, v___x_1526_);
return v___x_1529_;
}
}
static lean_object* _init_l_term_u03a3___x2c__(void){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_obj_once(&l_term_u03a3___x2c___00__closed__7, &l_term_u03a3___x2c___00__closed__7_once, _init_l_term_u03a3___x2c___00__closed__7);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(lean_object* v_x_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = ((lean_object*)(l_term_u03a3___x2c___00__closed__1));
lean_inc(v_x_1534_);
v___x_1538_ = l_Lean_Syntax_isOfKind(v_x_1534_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
lean_dec(v_x_1534_);
v___x_1539_ = lean_box(1);
v___x_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_a_1536_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1541_);
v___x_1543_ = lean_unsigned_to_nat(3u);
v___x_1544_ = l_Lean_Syntax_getArg(v_x_1534_, v___x_1543_);
lean_dec(v_x_1534_);
v___x_1545_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1546_ = l_Lean_expandExplicitBinders(v___x_1545_, v___x_1542_, v___x_1544_, v_a_1535_, v_a_1536_);
lean_dec(v___x_1542_);
return v___x_1546_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___boxed(lean_object* v_x_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1(v_x_1547_, v_a_1548_, v_a_1549_);
lean_dec_ref(v_a_1548_);
return v_res_1550_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__4(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = l_Lean_explicitBinders;
v___x_1558_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__3));
v___x_1559_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1560_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
lean_ctor_set(v___x_1560_, 2, v___x_1557_);
return v___x_1560_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__5(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = ((lean_object*)(l_Lean_unifConstraintElem___closed__7));
v___x_1562_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__4, &l_term_u03a3_x27___x2c___00__closed__4_once, _init_l_term_u03a3_x27___x2c___00__closed__4);
v___x_1563_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1564_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1562_);
lean_ctor_set(v___x_1564_, 2, v___x_1561_);
return v___x_1564_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__6(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1565_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__18));
v___x_1566_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__5, &l_term_u03a3_x27___x2c___00__closed__5_once, _init_l_term_u03a3_x27___x2c___00__closed__5);
v___x_1567_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1568_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1566_);
lean_ctor_set(v___x_1568_, 2, v___x_1565_);
return v___x_1568_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c___00__closed__7(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1569_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__6, &l_term_u03a3_x27___x2c___00__closed__6_once, _init_l_term_u03a3_x27___x2c___00__closed__6);
v___x_1570_ = lean_unsigned_to_nat(1022u);
v___x_1571_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
v___x_1572_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1570_);
lean_ctor_set(v___x_1572_, 2, v___x_1569_);
return v___x_1572_;
}
}
static lean_object* _init_l_term_u03a3_x27___x2c__(void){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_obj_once(&l_term_u03a3_x27___x2c___00__closed__7, &l_term_u03a3_x27___x2c___00__closed__7_once, _init_l_term_u03a3_x27___x2c___00__closed__7);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(lean_object* v_x_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = ((lean_object*)(l_term_u03a3_x27___x2c___00__closed__1));
lean_inc(v_x_1577_);
v___x_1581_ = l_Lean_Syntax_isOfKind(v_x_1577_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_x_1577_);
v___x_1582_ = lean_box(1);
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_a_1579_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1584_ = lean_unsigned_to_nat(1u);
v___x_1585_ = l_Lean_Syntax_getArg(v_x_1577_, v___x_1584_);
v___x_1586_ = lean_unsigned_to_nat(3u);
v___x_1587_ = l_Lean_Syntax_getArg(v_x_1577_, v___x_1586_);
lean_dec(v_x_1577_);
v___x_1588_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1589_ = l_Lean_expandExplicitBinders(v___x_1588_, v___x_1585_, v___x_1587_, v_a_1578_, v_a_1579_);
lean_dec(v___x_1585_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___boxed(lean_object* v_x_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1(v_x_1590_, v_a_1591_, v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1593_;
}
}
static lean_object* _init_l_term___xd7____1___closed__4(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1600_ = ((lean_object*)(l_term___xd7____1___closed__3));
v___x_1601_ = l_Lean_bracketedExplicitBinders;
v___x_1602_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1603_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1601_);
lean_ctor_set(v___x_1603_, 2, v___x_1600_);
return v___x_1603_;
}
}
static lean_object* _init_l_term___xd7____1___closed__6(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1607_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1608_ = lean_obj_once(&l_term___xd7____1___closed__4, &l_term___xd7____1___closed__4_once, _init_l_term___xd7____1___closed__4);
v___x_1609_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1610_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1608_);
lean_ctor_set(v___x_1610_, 2, v___x_1607_);
return v___x_1610_;
}
}
static lean_object* _init_l_term___xd7____1___closed__7(void){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1611_ = lean_obj_once(&l_term___xd7____1___closed__6, &l_term___xd7____1___closed__6_once, _init_l_term___xd7____1___closed__6);
v___x_1612_ = lean_unsigned_to_nat(35u);
v___x_1613_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_1614_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1613_);
lean_ctor_set(v___x_1614_, 1, v___x_1612_);
lean_ctor_set(v___x_1614_, 2, v___x_1611_);
return v___x_1614_;
}
}
static lean_object* _init_l_term___xd7____1(void){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = lean_obj_once(&l_term___xd7____1___closed__7, &l_term___xd7____1___closed__7_once, _init_l_term___xd7____1___closed__7);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(lean_object* v_x_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_term___xd7____1___closed__1));
lean_inc(v_x_1616_);
v___x_1620_ = l_Lean_Syntax_isOfKind(v_x_1616_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec(v_x_1616_);
v___x_1621_ = lean_box(1);
v___x_1622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v_a_1618_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = l_Lean_Syntax_getArg(v_x_1616_, v___x_1623_);
v___x_1625_ = lean_unsigned_to_nat(2u);
v___x_1626_ = l_Lean_Syntax_getArg(v_x_1616_, v___x_1625_);
lean_dec(v_x_1616_);
v___x_1627_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3___x2c____1___closed__1));
v___x_1628_ = l_Lean_expandBracketedBinders(v___x_1627_, v___x_1624_, v___x_1626_, v_a_1617_, v_a_1618_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7____1__1___boxed(lean_object* v_x_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l___aux__Init__NotationExtra______macroRules__term___xd7____1__1(v_x_1629_, v_a_1630_, v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1632_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__4(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1639_ = ((lean_object*)(l_term___xd7_x27____1___closed__3));
v___x_1640_ = l_Lean_bracketedExplicitBinders;
v___x_1641_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1642_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v___x_1640_);
lean_ctor_set(v___x_1642_, 2, v___x_1639_);
return v___x_1642_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__5(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = ((lean_object*)(l_term___xd7____1___closed__5));
v___x_1644_ = lean_obj_once(&l_term___xd7_x27____1___closed__4, &l_term___xd7_x27____1___closed__4_once, _init_l_term___xd7_x27____1___closed__4);
v___x_1645_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__4));
v___x_1646_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1644_);
lean_ctor_set(v___x_1646_, 2, v___x_1643_);
return v___x_1646_;
}
}
static lean_object* _init_l_term___xd7_x27____1___closed__6(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = lean_obj_once(&l_term___xd7_x27____1___closed__5, &l_term___xd7_x27____1___closed__5_once, _init_l_term___xd7_x27____1___closed__5);
v___x_1648_ = lean_unsigned_to_nat(35u);
v___x_1649_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_1650_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v___x_1648_);
lean_ctor_set(v___x_1650_, 2, v___x_1647_);
return v___x_1650_;
}
}
static lean_object* _init_l_term___xd7_x27____1(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_obj_once(&l_term___xd7_x27____1___closed__6, &l_term___xd7_x27____1___closed__6_once, _init_l_term___xd7_x27____1___closed__6);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(lean_object* v_x_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_){
_start:
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
lean_inc(v_x_1652_);
v___x_1656_ = l_Lean_Syntax_isOfKind(v_x_1652_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_dec(v_x_1652_);
v___x_1657_ = lean_box(1);
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_a_1654_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1659_);
v___x_1661_ = lean_unsigned_to_nat(2u);
v___x_1662_ = l_Lean_Syntax_getArg(v_x_1652_, v___x_1661_);
lean_dec(v_x_1652_);
v___x_1663_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_u03a3_x27___x2c____1___closed__1));
v___x_1664_ = l_Lean_expandBracketedBinders(v___x_1663_, v___x_1660_, v___x_1662_, v_a_1653_, v_a_1654_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1___boxed(lean_object* v_x_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___aux__Init__NotationExtra______macroRules__term___xd7_x27____1__1(v_x_1665_, v_a_1666_, v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(lean_object* v_x_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = ((lean_object*)(l_Lean_convCalc___00__closed__1));
lean_inc(v_x_1828_);
v___x_1832_ = l_Lean_Syntax_isOfKind(v_x_1828_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
lean_dec(v_x_1828_);
v___x_1833_ = lean_box(1);
v___x_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v_a_1830_);
return v___x_1834_;
}
else
{
lean_object* v_ref_1835_; lean_object* v___x_1836_; lean_object* v_tk_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_ref_1835_ = lean_ctor_get(v_a_1829_, 5);
v___x_1836_ = lean_unsigned_to_nat(0u);
v_tk_1837_ = l_Lean_Syntax_getArg(v_x_1828_, v___x_1836_);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = l_Lean_Syntax_getArg(v_x_1828_, v___x_1838_);
lean_dec(v_x_1828_);
v___x_1840_ = 0;
v___x_1841_ = l_Lean_SourceInfo_fromRef(v_ref_1835_, v___x_1840_);
v___x_1842_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__3));
v___x_1843_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__4));
lean_inc_n(v___x_1841_, 6);
v___x_1844_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1841_);
lean_ctor_set(v___x_1844_, 1, v___x_1843_);
v___x_1845_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_1846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1841_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_1848_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_1849_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1850_ = ((lean_object*)(l_Lean_calcTactic___closed__1));
v___x_1851_ = l_Lean_SourceInfo_fromRef(v_tk_1837_, v___x_1832_);
lean_dec(v_tk_1837_);
v___x_1852_ = ((lean_object*)(l_Lean_calc___closed__0));
v___x_1853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
v___x_1854_ = l_Lean_Syntax_node2(v___x_1841_, v___x_1850_, v___x_1853_, v___x_1839_);
v___x_1855_ = l_Lean_Syntax_node1(v___x_1841_, v___x_1849_, v___x_1854_);
v___x_1856_ = l_Lean_Syntax_node1(v___x_1841_, v___x_1848_, v___x_1855_);
v___x_1857_ = l_Lean_Syntax_node1(v___x_1841_, v___x_1847_, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_node3(v___x_1841_, v___x_1842_, v___x_1844_, v___x_1846_, v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v_a_1830_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___boxed(lean_object* v_x_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1(v_x_1860_, v_a_1861_, v_a_1862_);
lean_dec_ref(v_a_1861_);
return v_res_1863_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__9(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_unexpandUnit___redArg___closed__8));
v___x_1884_ = l_String_toRawSubstring_x27(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_unexpandUnit___redArg___closed__10(void){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_box(0);
v___x_1887_ = ((lean_object*)(l_unexpandUnit___redArg___closed__1));
v___x_1888_ = l_Lean_addMacroScope(v___x_1887_, v___x_1886_, v___x_1885_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg(lean_object* v_a_1901_, lean_object* v_a_1902_){
_start:
{
uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1903_ = 0;
v___x_1904_ = l_Lean_SourceInfo_fromRef(v_a_1901_, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
v___x_1906_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_1907_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_1904_, 6);
v___x_1908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1904_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_1910_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_1911_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_1912_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_1913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1904_);
lean_ctor_set(v___x_1913_, 1, v___x_1910_);
lean_ctor_set(v___x_1913_, 2, v___x_1911_);
lean_ctor_set(v___x_1913_, 3, v___x_1912_);
v___x_1914_ = l_Lean_Syntax_node1(v___x_1904_, v___x_1909_, v___x_1913_);
v___x_1915_ = l_Lean_Syntax_node2(v___x_1904_, v___x_1906_, v___x_1908_, v___x_1914_);
v___x_1916_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1917_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_1918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1904_);
lean_ctor_set(v___x_1918_, 1, v___x_1916_);
lean_ctor_set(v___x_1918_, 2, v___x_1917_);
v___x_1919_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_1920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1904_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_Syntax_node3(v___x_1904_, v___x_1905_, v___x_1915_, v___x_1918_, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v_a_1902_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___redArg___boxed(lean_object* v_a_1923_, lean_object* v_a_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_unexpandUnit___redArg(v_a_1923_, v_a_1924_);
lean_dec(v_a_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit(lean_object* v_x_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_unexpandUnit___redArg(v_a_1927_, v_a_1928_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_unexpandUnit___boxed(lean_object* v_x_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_unexpandUnit(v_x_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1931_);
lean_dec(v_x_1930_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg(lean_object* v_a_1938_, lean_object* v_a_1939_){
_start:
{
uint8_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1940_ = 0;
v___x_1941_ = l_Lean_SourceInfo_fromRef(v_a_1938_, v___x_1940_);
v___x_1942_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
v___x_1943_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_1941_, 3);
v___x_1944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1941_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1946_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_1947_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1941_);
lean_ctor_set(v___x_1947_, 1, v___x_1945_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
v___x_1948_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1949_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1941_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_Syntax_node3(v___x_1941_, v___x_1942_, v___x_1944_, v___x_1947_, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v_a_1939_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___redArg___boxed(lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_unexpandListNil___redArg(v_a_1952_, v_a_1953_);
lean_dec(v_a_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil(lean_object* v_x_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_unexpandListNil___redArg(v_a_1956_, v_a_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_unexpandListNil___boxed(lean_object* v_x_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_unexpandListNil(v_x_1959_, v_a_1960_, v_a_1961_);
lean_dec(v_a_1960_);
lean_dec(v_x_1959_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_unexpandListCons(lean_object* v_x_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; 
v___x_1972_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_1969_);
v___x_1973_ = l_Lean_Syntax_isOfKind(v_x_1969_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec(v_x_1969_);
v___x_1974_ = lean_box(0);
v___x_1975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v_a_1971_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1976_ = lean_unsigned_to_nat(1u);
v___x_1977_ = l_Lean_Syntax_getArg(v_x_1969_, v___x_1976_);
lean_dec(v_x_1969_);
v___x_1978_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1977_);
v___x_1979_ = l_Lean_Syntax_matchesNull(v___x_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v___x_1977_);
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_a_1971_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1982_ = lean_unsigned_to_nat(0u);
v___x_1983_ = l_Lean_Syntax_getArg(v___x_1977_, v___x_1982_);
v___x_1984_ = l_Lean_Syntax_getArg(v___x_1977_, v___x_1976_);
lean_dec(v___x_1977_);
v___x_1985_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_1984_);
v___x_1986_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_unexpandListCons___closed__1));
lean_inc(v___x_1984_);
v___x_1988_ = l_Lean_Syntax_isOfKind(v___x_1984_, v___x_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1989_);
lean_ctor_set(v___x_1990_, 1, v_a_1971_);
return v___x_1990_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1991_ = l_Lean_SourceInfo_fromRef(v_a_1970_, v___x_1986_);
v___x_1992_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_1991_, 4);
v___x_1993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_1995_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_1996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1991_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = l_Lean_Syntax_node3(v___x_1991_, v___x_1994_, v___x_1983_, v___x_1996_, v___x_1984_);
v___x_1998_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_1999_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1991_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = l_Lean_Syntax_node3(v___x_1991_, v___x_1985_, v___x_1993_, v___x_1997_, v___x_1999_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v_a_1971_);
return v___x_2001_;
}
}
else
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = l_Lean_Syntax_getArg(v___x_1984_, v___x_1976_);
lean_dec(v___x_1984_);
lean_inc(v___x_2002_);
v___x_2003_ = l_Lean_Syntax_matchesNull(v___x_2002_, v___x_1982_);
if (v___x_2003_ == 0)
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v___x_2004_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2005_ = l_Lean_Syntax_getArgs(v___x_2002_);
lean_dec(v___x_2002_);
v___x_2006_ = l_Lean_SourceInfo_fromRef(v_a_1970_, v___x_2003_);
v___x_2007_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2006_, 4);
v___x_2008_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2006_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2010_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2006_);
lean_ctor_set(v___x_2010_, 1, v___x_2004_);
v___x_2011_ = l_Array_mkArray2___redArg(v___x_1983_, v___x_2010_);
v___x_2012_ = l_Array_append___redArg(v___x_2011_, v___x_2005_);
lean_dec_ref(v___x_2005_);
v___x_2013_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2006_);
lean_ctor_set(v___x_2013_, 1, v___x_2009_);
lean_ctor_set(v___x_2013_, 2, v___x_2012_);
v___x_2014_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2015_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2006_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___x_2016_ = l_Lean_Syntax_node3(v___x_2006_, v___x_1985_, v___x_2008_, v___x_2013_, v___x_2015_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_a_1971_);
return v___x_2017_;
}
else
{
uint8_t v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v___x_2002_);
v___x_2018_ = 0;
v___x_2019_ = l_Lean_SourceInfo_fromRef(v_a_1970_, v___x_2018_);
v___x_2020_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2019_, 3);
v___x_2021_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2023_ = l_Lean_Syntax_node1(v___x_2019_, v___x_2022_, v___x_1983_);
v___x_2024_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2025_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2019_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_Syntax_node3(v___x_2019_, v___x_1985_, v___x_2021_, v___x_2023_, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
lean_ctor_set(v___x_2027_, 1, v_a_1971_);
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListCons___boxed(lean_object* v_x_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_unexpandListCons(v_x_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray(lean_object* v_x_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2036_);
v___x_2040_ = l_Lean_Syntax_isOfKind(v_x_2036_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec(v_x_2036_);
v___x_2041_ = lean_box(0);
v___x_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v_a_2038_);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2043_ = lean_unsigned_to_nat(1u);
v___x_2044_ = l_Lean_Syntax_getArg(v_x_2036_, v___x_2043_);
lean_dec(v_x_2036_);
lean_inc(v___x_2044_);
v___x_2045_ = l_Lean_Syntax_matchesNull(v___x_2044_, v___x_2043_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v___x_2047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v_a_2038_);
return v___x_2047_;
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = l_Lean_Syntax_getArg(v___x_2044_, v___x_2048_);
lean_dec(v___x_2044_);
v___x_2050_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2049_);
v___x_2051_ = l_Lean_Syntax_isOfKind(v___x_2049_, v___x_2050_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v___x_2049_);
v___x_2052_ = lean_box(0);
v___x_2053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v_a_2038_);
return v___x_2053_;
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2054_ = l_Lean_Syntax_getArg(v___x_2049_, v___x_2043_);
lean_dec(v___x_2049_);
v___x_2055_ = l_Lean_Syntax_getArgs(v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = 0;
v___x_2057_ = l_Lean_SourceInfo_fromRef(v_a_2037_, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_2059_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_2057_, 3);
v___x_2060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2057_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2062_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2063_ = l_Array_append___redArg(v___x_2062_, v___x_2055_);
lean_dec_ref(v___x_2055_);
v___x_2064_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2057_);
lean_ctor_set(v___x_2064_, 1, v___x_2061_);
lean_ctor_set(v___x_2064_, 2, v___x_2063_);
v___x_2065_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2066_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2057_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_Syntax_node3(v___x_2057_, v___x_2058_, v___x_2060_, v___x_2064_, v___x_2066_);
v___x_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
lean_ctor_set(v___x_2068_, 1, v_a_2038_);
return v___x_2068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandListToArray___boxed(lean_object* v_x_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_unexpandListToArray(v_x_2069_, v_a_2070_, v_a_2071_);
lean_dec(v_a_2070_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk(lean_object* v_x_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_){
_start:
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2073_);
v___x_2077_ = l_Lean_Syntax_isOfKind(v_x_2073_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
lean_dec(v_x_2073_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
lean_ctor_set(v___x_2079_, 1, v_a_2075_);
return v___x_2079_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = l_Lean_Syntax_getArg(v_x_2073_, v___x_2080_);
lean_dec(v_x_2073_);
v___x_2082_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2081_);
v___x_2083_ = l_Lean_Syntax_matchesNull(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2084_);
lean_ctor_set(v___x_2085_, 1, v_a_2075_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = l_Lean_Syntax_getArg(v___x_2081_, v___x_2086_);
v___x_2088_ = l_Lean_Syntax_getArg(v___x_2081_, v___x_2080_);
lean_dec(v___x_2081_);
v___x_2089_ = ((lean_object*)(l_unexpandUnit___redArg___closed__3));
lean_inc(v___x_2088_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v___x_2088_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2091_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2090_);
v___x_2092_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_2093_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2091_, 8);
v___x_2094_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2096_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2097_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2098_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2091_);
lean_ctor_set(v___x_2099_, 1, v___x_2096_);
lean_ctor_set(v___x_2099_, 2, v___x_2097_);
lean_ctor_set(v___x_2099_, 3, v___x_2098_);
v___x_2100_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2095_, v___x_2099_);
v___x_2101_ = l_Lean_Syntax_node2(v___x_2091_, v___x_2092_, v___x_2094_, v___x_2100_);
v___x_2102_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2103_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2104_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2091_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = l_Lean_Syntax_node1(v___x_2091_, v___x_2102_, v___x_2088_);
v___x_2106_ = l_Lean_Syntax_node3(v___x_2091_, v___x_2102_, v___x_2087_, v___x_2104_, v___x_2105_);
v___x_2107_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2091_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = l_Lean_Syntax_node3(v___x_2091_, v___x_2089_, v___x_2101_, v___x_2106_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v_a_2075_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = l_Lean_Syntax_getArg(v___x_2088_, v___x_2086_);
v___x_2112_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2111_);
v___x_2113_ = l_Lean_Syntax_isOfKind(v___x_2111_, v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_dec(v___x_2111_);
v___x_2114_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2113_);
v___x_2115_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2114_, 8);
v___x_2116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_2118_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2119_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2120_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2114_);
lean_ctor_set(v___x_2121_, 1, v___x_2118_);
lean_ctor_set(v___x_2121_, 2, v___x_2119_);
lean_ctor_set(v___x_2121_, 3, v___x_2120_);
v___x_2122_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2117_, v___x_2121_);
v___x_2123_ = l_Lean_Syntax_node2(v___x_2114_, v___x_2112_, v___x_2116_, v___x_2122_);
v___x_2124_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2125_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2126_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2114_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2124_, v___x_2088_);
v___x_2128_ = l_Lean_Syntax_node3(v___x_2114_, v___x_2124_, v___x_2087_, v___x_2126_, v___x_2127_);
v___x_2129_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2130_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2114_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_Syntax_node3(v___x_2114_, v___x_2089_, v___x_2123_, v___x_2128_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v_a_2075_);
return v___x_2132_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
v___x_2133_ = l_Lean_Syntax_getArg(v___x_2111_, v___x_2080_);
lean_dec(v___x_2111_);
v___x_2134_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2133_);
v___x_2135_ = l_Lean_Syntax_isOfKind(v___x_2133_, v___x_2134_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v___x_2133_);
v___x_2136_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2135_);
v___x_2137_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2136_, 8);
v___x_2138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2140_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2141_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2136_);
lean_ctor_set(v___x_2142_, 1, v___x_2139_);
lean_ctor_set(v___x_2142_, 2, v___x_2140_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
v___x_2143_ = l_Lean_Syntax_node1(v___x_2136_, v___x_2134_, v___x_2142_);
v___x_2144_ = l_Lean_Syntax_node2(v___x_2136_, v___x_2112_, v___x_2138_, v___x_2143_);
v___x_2145_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2146_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2136_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_Syntax_node1(v___x_2136_, v___x_2145_, v___x_2088_);
v___x_2149_ = l_Lean_Syntax_node3(v___x_2136_, v___x_2145_, v___x_2087_, v___x_2147_, v___x_2148_);
v___x_2150_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2136_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_Syntax_node3(v___x_2136_, v___x_2089_, v___x_2144_, v___x_2149_, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v_a_2075_);
return v___x_2153_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2154_ = l_Lean_Syntax_getArg(v___x_2133_, v___x_2086_);
lean_dec(v___x_2133_);
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Lean_Syntax_matchesIdent(v___x_2154_, v___x_2155_);
lean_dec(v___x_2154_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2157_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2156_);
v___x_2158_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2157_, 8);
v___x_2159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2161_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2162_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2163_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2157_);
lean_ctor_set(v___x_2163_, 1, v___x_2160_);
lean_ctor_set(v___x_2163_, 2, v___x_2161_);
lean_ctor_set(v___x_2163_, 3, v___x_2162_);
v___x_2164_ = l_Lean_Syntax_node1(v___x_2157_, v___x_2134_, v___x_2163_);
v___x_2165_ = l_Lean_Syntax_node2(v___x_2157_, v___x_2112_, v___x_2159_, v___x_2164_);
v___x_2166_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2167_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2157_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_Syntax_node1(v___x_2157_, v___x_2166_, v___x_2088_);
v___x_2170_ = l_Lean_Syntax_node3(v___x_2157_, v___x_2166_, v___x_2087_, v___x_2168_, v___x_2169_);
v___x_2171_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2157_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_Syntax_node3(v___x_2157_, v___x_2089_, v___x_2165_, v___x_2170_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_a_2075_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; 
v___x_2175_ = l_Lean_Syntax_getArg(v___x_2088_, v___x_2080_);
v___x_2176_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2175_);
v___x_2177_ = l_Lean_Syntax_matchesNull(v___x_2175_, v___x_2176_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v___x_2175_);
v___x_2178_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2177_);
v___x_2179_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2178_, 8);
v___x_2180_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2182_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2183_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2178_);
lean_ctor_set(v___x_2184_, 1, v___x_2181_);
lean_ctor_set(v___x_2184_, 2, v___x_2182_);
lean_ctor_set(v___x_2184_, 3, v___x_2183_);
v___x_2185_ = l_Lean_Syntax_node1(v___x_2178_, v___x_2134_, v___x_2184_);
v___x_2186_ = l_Lean_Syntax_node2(v___x_2178_, v___x_2112_, v___x_2180_, v___x_2185_);
v___x_2187_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2188_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2178_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_Syntax_node1(v___x_2178_, v___x_2187_, v___x_2088_);
v___x_2191_ = l_Lean_Syntax_node3(v___x_2178_, v___x_2187_, v___x_2087_, v___x_2189_, v___x_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2193_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2178_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = l_Lean_Syntax_node3(v___x_2178_, v___x_2089_, v___x_2186_, v___x_2191_, v___x_2193_);
v___x_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_a_2075_);
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
lean_dec(v___x_2088_);
v___x_2196_ = l_Lean_Syntax_getArg(v___x_2175_, v___x_2086_);
v___x_2197_ = l_Lean_Syntax_getArg(v___x_2175_, v___x_2082_);
lean_dec(v___x_2175_);
v___x_2198_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2199_ = l_Lean_Syntax_getArgs(v___x_2197_);
lean_dec(v___x_2197_);
v___x_2200_ = 0;
v___x_2201_ = l_Lean_SourceInfo_fromRef(v_a_2074_, v___x_2200_);
v___x_2202_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2201_, 8);
v___x_2203_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2201_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_2205_ = lean_obj_once(&l_unexpandUnit___redArg___closed__10, &l_unexpandUnit___redArg___closed__10_once, _init_l_unexpandUnit___redArg___closed__10);
v___x_2206_ = ((lean_object*)(l_unexpandUnit___redArg___closed__15));
v___x_2207_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2201_);
lean_ctor_set(v___x_2207_, 1, v___x_2204_);
lean_ctor_set(v___x_2207_, 2, v___x_2205_);
lean_ctor_set(v___x_2207_, 3, v___x_2206_);
v___x_2208_ = l_Lean_Syntax_node1(v___x_2201_, v___x_2134_, v___x_2207_);
v___x_2209_ = l_Lean_Syntax_node2(v___x_2201_, v___x_2112_, v___x_2203_, v___x_2208_);
v___x_2210_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2211_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2201_);
lean_ctor_set(v___x_2211_, 1, v___x_2198_);
lean_inc_ref(v___x_2211_);
v___x_2212_ = l_Array_mkArray2___redArg(v___x_2196_, v___x_2211_);
v___x_2213_ = l_Array_append___redArg(v___x_2212_, v___x_2199_);
lean_dec_ref(v___x_2199_);
v___x_2214_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2201_);
lean_ctor_set(v___x_2214_, 1, v___x_2210_);
lean_ctor_set(v___x_2214_, 2, v___x_2213_);
v___x_2215_ = l_Lean_Syntax_node3(v___x_2201_, v___x_2210_, v___x_2087_, v___x_2211_, v___x_2214_);
v___x_2216_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2217_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2201_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
v___x_2218_ = l_Lean_Syntax_node3(v___x_2201_, v___x_2089_, v___x_2209_, v___x_2215_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v_a_2075_);
return v___x_2219_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandProdMk___boxed(lean_object* v_x_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_unexpandProdMk(v_x_2220_, v_a_2221_, v_a_2222_);
lean_dec(v_a_2221_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_unexpandIte(lean_object* v_x_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2230_);
v___x_2234_ = l_Lean_Syntax_isOfKind(v_x_2230_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_dec(v_x_2230_);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2235_);
lean_ctor_set(v___x_2236_, 1, v_a_2232_);
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = l_Lean_Syntax_getArg(v_x_2230_, v___x_2237_);
lean_dec(v_x_2230_);
v___x_2239_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2238_);
v___x_2240_ = l_Lean_Syntax_matchesNull(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_a_2232_);
return v___x_2242_;
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v___x_2244_ = l_Lean_Syntax_getArg(v___x_2238_, v___x_2243_);
v___x_2245_ = l_Lean_Syntax_getArg(v___x_2238_, v___x_2237_);
v___x_2246_ = lean_unsigned_to_nat(2u);
v___x_2247_ = l_Lean_Syntax_getArg(v___x_2238_, v___x_2246_);
lean_dec(v___x_2238_);
v___x_2248_ = 0;
v___x_2249_ = l_Lean_SourceInfo_fromRef(v_a_2231_, v___x_2248_);
v___x_2250_ = ((lean_object*)(l_unexpandIte___closed__1));
v___x_2251_ = ((lean_object*)(l_unexpandIte___closed__2));
lean_inc_n(v___x_2249_, 3);
v___x_2252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2249_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_unexpandIte___closed__3));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2249_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = ((lean_object*)(l_unexpandIte___closed__4));
v___x_2256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2249_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_Syntax_node6(v___x_2249_, v___x_2250_, v___x_2252_, v___x_2244_, v___x_2254_, v___x_2245_, v___x_2256_, v___x_2247_);
v___x_2258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v_a_2232_);
return v___x_2258_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandIte___boxed(lean_object* v_x_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_unexpandIte(v_x_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2260_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec(lean_object* v_x_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v___x_2273_; uint8_t v___x_2274_; 
v___x_2273_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2270_);
v___x_2274_ = l_Lean_Syntax_isOfKind(v_x_2270_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec(v_x_2270_);
v___x_2275_ = lean_box(0);
v___x_2276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v_a_2272_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; uint8_t v___x_2280_; 
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = l_Lean_Syntax_getArg(v_x_2270_, v___x_2277_);
lean_dec(v_x_2270_);
v___x_2279_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2278_);
v___x_2280_ = l_Lean_Syntax_matchesNull(v___x_2278_, v___x_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v___x_2278_);
v___x_2281_ = lean_box(0);
v___x_2282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
lean_ctor_set(v___x_2282_, 1, v_a_2272_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2283_ = lean_unsigned_to_nat(0u);
v___x_2284_ = l_Lean_Syntax_getArg(v___x_2278_, v___x_2283_);
v___x_2285_ = l_Lean_Syntax_getArg(v___x_2278_, v___x_2277_);
lean_dec(v___x_2278_);
v___x_2286_ = 0;
v___x_2287_ = l_Lean_SourceInfo_fromRef(v_a_2271_, v___x_2286_);
v___x_2288_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2289_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc(v___x_2287_);
v___x_2290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2287_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_Syntax_node3(v___x_2287_, v___x_2288_, v___x_2285_, v___x_2290_, v___x_2284_);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v_a_2272_);
return v___x_2292_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqNDRec___boxed(lean_object* v_x_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_unexpandEqNDRec(v_x_2293_, v_a_2294_, v_a_2295_);
lean_dec(v_a_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec(lean_object* v_x_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2297_);
v___x_2301_ = l_Lean_Syntax_isOfKind(v_x_2297_, v___x_2300_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
lean_dec(v_x_2297_);
v___x_2302_ = lean_box(0);
v___x_2303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_a_2299_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = l_Lean_Syntax_getArg(v_x_2297_, v___x_2304_);
lean_dec(v_x_2297_);
v___x_2306_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2305_);
v___x_2307_ = l_Lean_Syntax_matchesNull(v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v___x_2309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v_a_2299_);
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_Lean_Syntax_getArg(v___x_2305_, v___x_2310_);
v___x_2312_ = l_Lean_Syntax_getArg(v___x_2305_, v___x_2304_);
lean_dec(v___x_2305_);
v___x_2313_ = 0;
v___x_2314_ = l_Lean_SourceInfo_fromRef(v_a_2298_, v___x_2313_);
v___x_2315_ = ((lean_object*)(l_unexpandEqNDRec___closed__1));
v___x_2316_ = ((lean_object*)(l_unexpandEqNDRec___closed__2));
lean_inc(v___x_2314_);
v___x_2317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = l_Lean_Syntax_node3(v___x_2314_, v___x_2315_, v___x_2312_, v___x_2317_, v___x_2311_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2318_);
lean_ctor_set(v___x_2319_, 1, v_a_2299_);
return v___x_2319_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandEqRec___boxed(lean_object* v_x_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_unexpandEqRec(v_x_2320_, v_a_2321_, v_a_2322_);
lean_dec(v_a_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_unexpandExists(lean_object* v_x_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2337_; uint8_t v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2334_);
v___x_2338_ = l_Lean_Syntax_isOfKind(v_x_2334_, v___x_2337_);
if (v___x_2338_ == 0)
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_x_2334_);
v___x_2339_ = lean_box(0);
v___x_2340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v_a_2336_);
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = l_Lean_Syntax_getArg(v_x_2334_, v___x_2341_);
lean_dec(v_x_2334_);
lean_inc(v___x_2342_);
v___x_2343_ = l_Lean_Syntax_matchesNull(v___x_2342_, v___x_2341_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_dec(v___x_2342_);
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v_a_2336_);
return v___x_2345_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = l_Lean_Syntax_getArg(v___x_2342_, v___x_2346_);
lean_dec(v___x_2342_);
v___x_2348_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2347_);
v___x_2349_ = l_Lean_Syntax_isOfKind(v___x_2347_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v___x_2351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_ctor_set(v___x_2351_, 1, v_a_2336_);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2352_ = l_Lean_Syntax_getArg(v___x_2347_, v___x_2341_);
lean_dec(v___x_2347_);
v___x_2353_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2352_);
v___x_2354_ = l_Lean_Syntax_isOfKind(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v___x_2356_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
lean_ctor_set(v___x_2356_, 1, v_a_2336_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = l_Lean_Syntax_getArg(v___x_2352_, v___x_2346_);
lean_inc(v___x_2357_);
v___x_2358_ = l_Lean_Syntax_matchesNull(v___x_2357_, v___x_2341_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec(v___x_2357_);
lean_dec(v___x_2352_);
v___x_2359_ = lean_box(0);
v___x_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
lean_ctor_set(v___x_2360_, 1, v_a_2336_);
return v___x_2360_;
}
else
{
lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2361_ = l_Lean_Syntax_getArg(v___x_2357_, v___x_2346_);
lean_dec(v___x_2357_);
v___x_2362_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2361_);
v___x_2363_ = l_Lean_Syntax_isOfKind(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2361_);
v___x_2365_ = l_Lean_Syntax_isOfKind(v___x_2361_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
lean_ctor_set(v___x_2367_, 1, v_a_2336_);
return v___x_2367_;
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; uint8_t v___x_2370_; 
v___x_2368_ = l_Lean_Syntax_getArg(v___x_2361_, v___x_2346_);
v___x_2369_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2368_);
v___x_2370_ = l_Lean_Syntax_isOfKind(v___x_2368_, v___x_2369_);
if (v___x_2370_ == 0)
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v___x_2368_);
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v_a_2336_);
return v___x_2372_;
}
else
{
lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v___x_2373_ = l_Lean_Syntax_getArg(v___x_2368_, v___x_2341_);
lean_dec(v___x_2368_);
v___x_2374_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2373_);
v___x_2375_ = l_Lean_Syntax_isOfKind(v___x_2373_, v___x_2374_);
if (v___x_2375_ == 0)
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec(v___x_2373_);
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v_a_2336_);
return v___x_2377_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2378_ = l_Lean_Syntax_getArg(v___x_2373_, v___x_2346_);
lean_dec(v___x_2373_);
v___x_2379_ = lean_box(0);
v___x_2380_ = l_Lean_Syntax_matchesIdent(v___x_2378_, v___x_2379_);
lean_dec(v___x_2378_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2381_ = lean_box(0);
v___x_2382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
lean_ctor_set(v___x_2382_, 1, v_a_2336_);
return v___x_2382_;
}
else
{
lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = l_Lean_Syntax_getArg(v___x_2361_, v___x_2341_);
lean_inc(v___x_2383_);
v___x_2384_ = l_Lean_Syntax_isOfKind(v___x_2383_, v___x_2362_);
if (v___x_2384_ == 0)
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_dec(v___x_2383_);
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2385_ = lean_box(0);
v___x_2386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_a_2336_);
return v___x_2386_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = lean_unsigned_to_nat(3u);
v___x_2388_ = l_Lean_Syntax_getArg(v___x_2361_, v___x_2387_);
lean_dec(v___x_2361_);
lean_inc(v___x_2388_);
v___x_2389_ = l_Lean_Syntax_matchesNull(v___x_2388_, v___x_2341_);
if (v___x_2389_ == 0)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v___x_2388_);
lean_dec(v___x_2383_);
lean_dec(v___x_2352_);
v___x_2390_ = lean_box(0);
v___x_2391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
lean_ctor_set(v___x_2391_, 1, v_a_2336_);
return v___x_2391_;
}
else
{
lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2392_ = l_Lean_Syntax_getArg(v___x_2352_, v___x_2341_);
v___x_2393_ = l_Lean_Syntax_matchesNull(v___x_2392_, v___x_2346_);
if (v___x_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec(v___x_2388_);
lean_dec(v___x_2383_);
lean_dec(v___x_2352_);
v___x_2394_ = lean_box(0);
v___x_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
lean_ctor_set(v___x_2395_, 1, v_a_2336_);
return v___x_2395_;
}
else
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2396_ = l_Lean_Syntax_getArg(v___x_2388_, v___x_2346_);
lean_dec(v___x_2388_);
v___x_2397_ = l_Lean_Syntax_getArg(v___x_2352_, v___x_2387_);
lean_dec(v___x_2352_);
v___x_2398_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2363_);
v___x_2399_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
v___x_2400_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2398_, 10);
v___x_2401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2398_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2403_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2404_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2405_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_2406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2398_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2408_ = l_Lean_Syntax_node1(v___x_2398_, v___x_2407_, v___x_2383_);
v___x_2409_ = l_Lean_Syntax_node1(v___x_2398_, v___x_2403_, v___x_2408_);
v___x_2410_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2398_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2398_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_Syntax_node5(v___x_2398_, v___x_2404_, v___x_2406_, v___x_2409_, v___x_2411_, v___x_2396_, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node1(v___x_2398_, v___x_2403_, v___x_2414_);
v___x_2416_ = l_Lean_Syntax_node1(v___x_2398_, v___x_2402_, v___x_2415_);
v___x_2417_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2398_);
lean_ctor_set(v___x_2418_, 1, v___x_2417_);
v___x_2419_ = l_Lean_Syntax_node4(v___x_2398_, v___x_2399_, v___x_2401_, v___x_2416_, v___x_2418_, v___x_2397_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_a_2336_);
return v___x_2420_;
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
lean_object* v___x_2421_; uint8_t v___x_2422_; 
v___x_2421_ = l_Lean_Syntax_getArg(v___x_2352_, v___x_2341_);
v___x_2422_ = l_Lean_Syntax_matchesNull(v___x_2421_, v___x_2346_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v___x_2361_);
lean_dec(v___x_2352_);
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v_a_2336_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; 
v___x_2425_ = lean_unsigned_to_nat(3u);
v___x_2426_ = l_Lean_Syntax_getArg(v___x_2352_, v___x_2425_);
lean_dec(v___x_2352_);
v___x_2427_ = ((lean_object*)(l_term_u2203___x2c___00__closed__1));
lean_inc(v___x_2426_);
v___x_2428_ = l_Lean_Syntax_isOfKind(v___x_2426_, v___x_2427_);
if (v___x_2428_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2429_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2428_);
v___x_2430_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2429_, 7);
v___x_2431_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2429_);
lean_ctor_set(v___x_2431_, 1, v___x_2430_);
v___x_2432_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
v___x_2433_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2434_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2435_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2436_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2435_, v___x_2361_);
v___x_2437_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2434_, v___x_2436_);
v___x_2438_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2439_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2429_);
lean_ctor_set(v___x_2439_, 1, v___x_2434_);
lean_ctor_set(v___x_2439_, 2, v___x_2438_);
v___x_2440_ = l_Lean_Syntax_node2(v___x_2429_, v___x_2433_, v___x_2437_, v___x_2439_);
v___x_2441_ = l_Lean_Syntax_node1(v___x_2429_, v___x_2432_, v___x_2440_);
v___x_2442_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2443_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2429_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node4(v___x_2429_, v___x_2427_, v___x_2431_, v___x_2441_, v___x_2443_, v___x_2426_);
v___x_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
lean_ctor_set(v___x_2445_, 1, v_a_2336_);
return v___x_2445_;
}
else
{
lean_object* v___x_2446_; lean_object* v___x_2447_; uint8_t v___x_2448_; 
v___x_2446_ = l_Lean_Syntax_getArg(v___x_2426_, v___x_2341_);
v___x_2447_ = ((lean_object*)(l_Lean_explicitBinders___closed__1));
lean_inc(v___x_2446_);
v___x_2448_ = l_Lean_Syntax_isOfKind(v___x_2446_, v___x_2447_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
lean_dec(v___x_2446_);
v___x_2449_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2448_);
v___x_2450_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2449_, 7);
v___x_2451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2451_, 0, v___x_2449_);
lean_ctor_set(v___x_2451_, 1, v___x_2450_);
v___x_2452_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
v___x_2453_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2454_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2455_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2454_, v___x_2361_);
v___x_2456_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2453_, v___x_2455_);
v___x_2457_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2458_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2449_);
lean_ctor_set(v___x_2458_, 1, v___x_2453_);
lean_ctor_set(v___x_2458_, 2, v___x_2457_);
v___x_2459_ = l_Lean_Syntax_node2(v___x_2449_, v___x_2452_, v___x_2456_, v___x_2458_);
v___x_2460_ = l_Lean_Syntax_node1(v___x_2449_, v___x_2447_, v___x_2459_);
v___x_2461_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2462_, 0, v___x_2449_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
v___x_2463_ = l_Lean_Syntax_node4(v___x_2449_, v___x_2427_, v___x_2451_, v___x_2460_, v___x_2462_, v___x_2426_);
v___x_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v_a_2336_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2465_ = l_Lean_Syntax_getArg(v___x_2446_, v___x_2346_);
lean_dec(v___x_2446_);
v___x_2466_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__2));
lean_inc(v___x_2465_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v___x_2465_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
lean_dec(v___x_2465_);
v___x_2468_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2467_);
v___x_2469_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2468_, 7);
v___x_2470_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2472_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2473_ = l_Lean_Syntax_node1(v___x_2468_, v___x_2472_, v___x_2361_);
v___x_2474_ = l_Lean_Syntax_node1(v___x_2468_, v___x_2471_, v___x_2473_);
v___x_2475_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2476_, 0, v___x_2468_);
lean_ctor_set(v___x_2476_, 1, v___x_2471_);
lean_ctor_set(v___x_2476_, 2, v___x_2475_);
v___x_2477_ = l_Lean_Syntax_node2(v___x_2468_, v___x_2466_, v___x_2474_, v___x_2476_);
v___x_2478_ = l_Lean_Syntax_node1(v___x_2468_, v___x_2447_, v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2480_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2468_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_Syntax_node4(v___x_2468_, v___x_2427_, v___x_2470_, v___x_2478_, v___x_2480_, v___x_2426_);
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2481_);
lean_ctor_set(v___x_2482_, 1, v_a_2336_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = l_Lean_Syntax_getArg(v___x_2465_, v___x_2341_);
v___x_2484_ = l_Lean_Syntax_matchesNull(v___x_2483_, v___x_2346_);
if (v___x_2484_ == 0)
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v___x_2465_);
v___x_2485_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2484_);
v___x_2486_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2485_, 7);
v___x_2487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2487_, 0, v___x_2485_);
lean_ctor_set(v___x_2487_, 1, v___x_2486_);
v___x_2488_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2489_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2490_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2489_, v___x_2361_);
v___x_2491_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2488_, v___x_2490_);
v___x_2492_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2485_);
lean_ctor_set(v___x_2493_, 1, v___x_2488_);
lean_ctor_set(v___x_2493_, 2, v___x_2492_);
v___x_2494_ = l_Lean_Syntax_node2(v___x_2485_, v___x_2466_, v___x_2491_, v___x_2493_);
v___x_2495_ = l_Lean_Syntax_node1(v___x_2485_, v___x_2447_, v___x_2494_);
v___x_2496_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2485_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node4(v___x_2485_, v___x_2427_, v___x_2487_, v___x_2495_, v___x_2497_, v___x_2426_);
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
lean_ctor_set(v___x_2499_, 1, v_a_2336_);
return v___x_2499_;
}
else
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_xs_2503_; uint8_t v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2500_ = l_Lean_Syntax_getArg(v___x_2465_, v___x_2346_);
lean_dec(v___x_2465_);
v___x_2501_ = l_Lean_Syntax_getArg(v___x_2426_, v___x_2425_);
lean_dec(v___x_2426_);
v___x_2502_ = ((lean_object*)(l_unexpandExists___closed__3));
v_xs_2503_ = l_Lean_Syntax_getArgs(v___x_2500_);
lean_dec(v___x_2500_);
v___x_2504_ = 0;
v___x_2505_ = l_Lean_SourceInfo_fromRef(v_a_2335_, v___x_2504_);
v___x_2506_ = ((lean_object*)(l_term_u2203___x2c___00__closed__2));
lean_inc_n(v___x_2505_, 7);
v___x_2507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2509_ = l_Lean_Syntax_node1(v___x_2505_, v___x_2502_, v___x_2361_);
v___x_2510_ = l_Array_mkArray1___redArg(v___x_2509_);
v___x_2511_ = l_Array_append___redArg(v___x_2510_, v_xs_2503_);
lean_dec_ref(v_xs_2503_);
v___x_2512_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2505_);
lean_ctor_set(v___x_2512_, 1, v___x_2508_);
lean_ctor_set(v___x_2512_, 2, v___x_2511_);
v___x_2513_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2505_);
lean_ctor_set(v___x_2514_, 1, v___x_2508_);
lean_ctor_set(v___x_2514_, 2, v___x_2513_);
v___x_2515_ = l_Lean_Syntax_node2(v___x_2505_, v___x_2466_, v___x_2512_, v___x_2514_);
v___x_2516_ = l_Lean_Syntax_node1(v___x_2505_, v___x_2447_, v___x_2515_);
v___x_2517_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_2518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2505_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_Syntax_node4(v___x_2505_, v___x_2427_, v___x_2507_, v___x_2516_, v___x_2518_, v___x_2501_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v_a_2336_);
return v___x_2520_;
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
LEAN_EXPORT lean_object* l_unexpandExists___boxed(lean_object* v_x_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_unexpandExists(v_x_2521_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2522_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_unexpandSigma(lean_object* v_x_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2526_);
v___x_2530_ = l_Lean_Syntax_isOfKind(v_x_2526_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_x_2526_);
v___x_2531_ = lean_box(0);
v___x_2532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_a_2528_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = l_Lean_Syntax_getArg(v_x_2526_, v___x_2533_);
lean_dec(v_x_2526_);
lean_inc(v___x_2534_);
v___x_2535_ = l_Lean_Syntax_matchesNull(v___x_2534_, v___x_2533_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v___x_2534_);
v___x_2536_ = lean_box(0);
v___x_2537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2536_);
lean_ctor_set(v___x_2537_, 1, v_a_2528_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2538_ = lean_unsigned_to_nat(0u);
v___x_2539_ = l_Lean_Syntax_getArg(v___x_2534_, v___x_2538_);
lean_dec(v___x_2534_);
v___x_2540_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2539_);
v___x_2541_ = l_Lean_Syntax_isOfKind(v___x_2539_, v___x_2540_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v___x_2543_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v_a_2528_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2544_ = l_Lean_Syntax_getArg(v___x_2539_, v___x_2533_);
lean_dec(v___x_2539_);
v___x_2545_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2544_);
v___x_2546_ = l_Lean_Syntax_isOfKind(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v___x_2548_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
lean_ctor_set(v___x_2548_, 1, v_a_2528_);
return v___x_2548_;
}
else
{
lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2549_ = l_Lean_Syntax_getArg(v___x_2544_, v___x_2538_);
lean_inc(v___x_2549_);
v___x_2550_ = l_Lean_Syntax_matchesNull(v___x_2549_, v___x_2533_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v___x_2549_);
lean_dec(v___x_2544_);
v___x_2551_ = lean_box(0);
v___x_2552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
lean_ctor_set(v___x_2552_, 1, v_a_2528_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2553_ = l_Lean_Syntax_getArg(v___x_2549_, v___x_2538_);
lean_dec(v___x_2549_);
v___x_2554_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2553_);
v___x_2555_ = l_Lean_Syntax_isOfKind(v___x_2553_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v___x_2553_);
lean_dec(v___x_2544_);
v___x_2556_ = lean_box(0);
v___x_2557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v_a_2528_);
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = l_Lean_Syntax_getArg(v___x_2553_, v___x_2538_);
v___x_2559_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2558_);
v___x_2560_ = l_Lean_Syntax_isOfKind(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v___x_2558_);
lean_dec(v___x_2553_);
lean_dec(v___x_2544_);
v___x_2561_ = lean_box(0);
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v___x_2561_);
lean_ctor_set(v___x_2562_, 1, v_a_2528_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = l_Lean_Syntax_getArg(v___x_2558_, v___x_2533_);
lean_dec(v___x_2558_);
v___x_2564_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2563_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v___x_2563_);
lean_dec(v___x_2553_);
lean_dec(v___x_2544_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v_a_2528_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = l_Lean_Syntax_getArg(v___x_2563_, v___x_2538_);
lean_dec(v___x_2563_);
v___x_2569_ = lean_box(0);
v___x_2570_ = l_Lean_Syntax_matchesIdent(v___x_2568_, v___x_2569_);
lean_dec(v___x_2568_);
if (v___x_2570_ == 0)
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
lean_dec(v___x_2553_);
lean_dec(v___x_2544_);
v___x_2571_ = lean_box(0);
v___x_2572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
lean_ctor_set(v___x_2572_, 1, v_a_2528_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = l_Lean_Syntax_getArg(v___x_2553_, v___x_2533_);
v___x_2574_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2573_);
v___x_2575_ = l_Lean_Syntax_isOfKind(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
lean_dec(v___x_2573_);
lean_dec(v___x_2553_);
lean_dec(v___x_2544_);
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
lean_ctor_set(v___x_2577_, 1, v_a_2528_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2578_ = lean_unsigned_to_nat(3u);
v___x_2579_ = l_Lean_Syntax_getArg(v___x_2553_, v___x_2578_);
lean_dec(v___x_2553_);
lean_inc(v___x_2579_);
v___x_2580_ = l_Lean_Syntax_matchesNull(v___x_2579_, v___x_2533_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec(v___x_2579_);
lean_dec(v___x_2573_);
lean_dec(v___x_2544_);
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
lean_ctor_set(v___x_2582_, 1, v_a_2528_);
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = l_Lean_Syntax_getArg(v___x_2544_, v___x_2533_);
v___x_2584_ = l_Lean_Syntax_matchesNull(v___x_2583_, v___x_2538_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v___x_2579_);
lean_dec(v___x_2573_);
lean_dec(v___x_2544_);
v___x_2585_ = lean_box(0);
v___x_2586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v_a_2528_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2587_ = l_Lean_Syntax_getArg(v___x_2579_, v___x_2538_);
lean_dec(v___x_2579_);
v___x_2588_ = l_Lean_Syntax_getArg(v___x_2544_, v___x_2578_);
lean_dec(v___x_2544_);
v___x_2589_ = 0;
v___x_2590_ = l_Lean_SourceInfo_fromRef(v_a_2527_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l_term___xd7____1___closed__1));
v___x_2592_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2593_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2590_, 7);
v___x_2594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2590_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2596_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2597_ = l_Lean_Syntax_node1(v___x_2590_, v___x_2596_, v___x_2573_);
v___x_2598_ = l_Lean_Syntax_node1(v___x_2590_, v___x_2595_, v___x_2597_);
v___x_2599_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2590_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2590_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node5(v___x_2590_, v___x_2592_, v___x_2594_, v___x_2598_, v___x_2600_, v___x_2587_, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_unexpandSigma___closed__0));
v___x_2605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2590_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l_Lean_Syntax_node3(v___x_2590_, v___x_2591_, v___x_2603_, v___x_2605_, v___x_2588_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v_a_2528_);
return v___x_2607_;
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
LEAN_EXPORT lean_object* l_unexpandSigma___boxed(lean_object* v_x_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v_res_2611_; 
v_res_2611_ = l_unexpandSigma(v_x_2608_, v_a_2609_, v_a_2610_);
lean_dec(v_a_2609_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l_unexpandPSigma(lean_object* v_x_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_){
_start:
{
lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2613_);
v___x_2617_ = l_Lean_Syntax_isOfKind(v_x_2613_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v_x_2613_);
v___x_2618_ = lean_box(0);
v___x_2619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v_a_2615_);
return v___x_2619_;
}
else
{
lean_object* v___x_2620_; lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = l_Lean_Syntax_getArg(v_x_2613_, v___x_2620_);
lean_dec(v_x_2613_);
lean_inc(v___x_2621_);
v___x_2622_ = l_Lean_Syntax_matchesNull(v___x_2621_, v___x_2620_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v___x_2621_);
v___x_2623_ = lean_box(0);
v___x_2624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v_a_2615_);
return v___x_2624_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2625_ = lean_unsigned_to_nat(0u);
v___x_2626_ = l_Lean_Syntax_getArg(v___x_2621_, v___x_2625_);
lean_dec(v___x_2621_);
v___x_2627_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2626_);
v___x_2628_ = l_Lean_Syntax_isOfKind(v___x_2626_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v___x_2630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
lean_ctor_set(v___x_2630_, 1, v_a_2615_);
return v___x_2630_;
}
else
{
lean_object* v___x_2631_; lean_object* v___x_2632_; uint8_t v___x_2633_; 
v___x_2631_ = l_Lean_Syntax_getArg(v___x_2626_, v___x_2620_);
lean_dec(v___x_2626_);
v___x_2632_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2631_);
v___x_2633_ = l_Lean_Syntax_isOfKind(v___x_2631_, v___x_2632_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v___x_2631_);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2635_, 0, v___x_2634_);
lean_ctor_set(v___x_2635_, 1, v_a_2615_);
return v___x_2635_;
}
else
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = l_Lean_Syntax_getArg(v___x_2631_, v___x_2625_);
lean_inc(v___x_2636_);
v___x_2637_ = l_Lean_Syntax_matchesNull(v___x_2636_, v___x_2620_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_dec(v___x_2636_);
lean_dec(v___x_2631_);
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
lean_ctor_set(v___x_2639_, 1, v_a_2615_);
return v___x_2639_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2640_ = l_Lean_Syntax_getArg(v___x_2636_, v___x_2625_);
lean_dec(v___x_2636_);
v___x_2641_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2640_);
v___x_2642_ = l_Lean_Syntax_isOfKind(v___x_2640_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_dec(v___x_2640_);
lean_dec(v___x_2631_);
v___x_2643_ = lean_box(0);
v___x_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
lean_ctor_set(v___x_2644_, 1, v_a_2615_);
return v___x_2644_;
}
else
{
lean_object* v___x_2645_; lean_object* v___x_2646_; uint8_t v___x_2647_; 
v___x_2645_ = l_Lean_Syntax_getArg(v___x_2640_, v___x_2625_);
v___x_2646_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2645_);
v___x_2647_ = l_Lean_Syntax_isOfKind(v___x_2645_, v___x_2646_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec(v___x_2645_);
lean_dec(v___x_2640_);
lean_dec(v___x_2631_);
v___x_2648_ = lean_box(0);
v___x_2649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v_a_2615_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2650_ = l_Lean_Syntax_getArg(v___x_2645_, v___x_2620_);
lean_dec(v___x_2645_);
v___x_2651_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2650_);
v___x_2652_ = l_Lean_Syntax_isOfKind(v___x_2650_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec(v___x_2650_);
lean_dec(v___x_2640_);
lean_dec(v___x_2631_);
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
lean_ctor_set(v___x_2654_, 1, v_a_2615_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2655_ = l_Lean_Syntax_getArg(v___x_2650_, v___x_2625_);
lean_dec(v___x_2650_);
v___x_2656_ = lean_box(0);
v___x_2657_ = l_Lean_Syntax_matchesIdent(v___x_2655_, v___x_2656_);
lean_dec(v___x_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec(v___x_2640_);
lean_dec(v___x_2631_);
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v_a_2615_);
return v___x_2659_;
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2660_ = l_Lean_Syntax_getArg(v___x_2640_, v___x_2620_);
v___x_2661_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2660_);
v___x_2662_ = l_Lean_Syntax_isOfKind(v___x_2660_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec(v___x_2660_);
lean_dec(v___x_2640_);
lean_dec(v___x_2631_);
v___x_2663_ = lean_box(0);
v___x_2664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v_a_2615_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_unsigned_to_nat(3u);
v___x_2666_ = l_Lean_Syntax_getArg(v___x_2640_, v___x_2665_);
lean_dec(v___x_2640_);
lean_inc(v___x_2666_);
v___x_2667_ = l_Lean_Syntax_matchesNull(v___x_2666_, v___x_2620_);
if (v___x_2667_ == 0)
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v___x_2666_);
lean_dec(v___x_2660_);
lean_dec(v___x_2631_);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v_a_2615_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = l_Lean_Syntax_getArg(v___x_2631_, v___x_2620_);
v___x_2671_ = l_Lean_Syntax_matchesNull(v___x_2670_, v___x_2625_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec(v___x_2666_);
lean_dec(v___x_2660_);
lean_dec(v___x_2631_);
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v_a_2615_);
return v___x_2673_;
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2674_ = l_Lean_Syntax_getArg(v___x_2666_, v___x_2625_);
lean_dec(v___x_2666_);
v___x_2675_ = l_Lean_Syntax_getArg(v___x_2631_, v___x_2665_);
lean_dec(v___x_2631_);
v___x_2676_ = 0;
v___x_2677_ = l_Lean_SourceInfo_fromRef(v_a_2614_, v___x_2676_);
v___x_2678_ = ((lean_object*)(l_term___xd7_x27____1___closed__1));
v___x_2679_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__1));
v___x_2680_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_2677_, 7);
v___x_2681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2681_, 0, v___x_2677_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
v___x_2682_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2683_ = ((lean_object*)(l_unexpandExists___closed__3));
v___x_2684_ = l_Lean_Syntax_node1(v___x_2677_, v___x_2683_, v___x_2660_);
v___x_2685_ = l_Lean_Syntax_node1(v___x_2677_, v___x_2682_, v___x_2684_);
v___x_2686_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2677_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_2689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2677_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_Lean_Syntax_node5(v___x_2677_, v___x_2679_, v___x_2681_, v___x_2685_, v___x_2687_, v___x_2674_, v___x_2689_);
v___x_2691_ = ((lean_object*)(l_unexpandPSigma___closed__0));
v___x_2692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2677_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l_Lean_Syntax_node3(v___x_2677_, v___x_2678_, v___x_2690_, v___x_2692_, v___x_2675_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2693_);
lean_ctor_set(v___x_2694_, 1, v_a_2615_);
return v___x_2694_;
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
LEAN_EXPORT lean_object* l_unexpandPSigma___boxed(lean_object* v_x_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_unexpandPSigma(v_x_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_unexpandSubtype(lean_object* v_x_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2708_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2705_);
v___x_2709_ = l_Lean_Syntax_isOfKind(v_x_2705_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec(v_x_2705_);
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v_a_2707_);
return v___x_2711_;
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = l_Lean_Syntax_getArg(v_x_2705_, v___x_2712_);
lean_dec(v_x_2705_);
lean_inc(v___x_2713_);
v___x_2714_ = l_Lean_Syntax_matchesNull(v___x_2713_, v___x_2712_);
if (v___x_2714_ == 0)
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_dec(v___x_2713_);
v___x_2715_ = lean_box(0);
v___x_2716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v_a_2707_);
return v___x_2716_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; uint8_t v___x_2720_; 
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = l_Lean_Syntax_getArg(v___x_2713_, v___x_2717_);
lean_dec(v___x_2713_);
v___x_2719_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__7));
lean_inc(v___x_2718_);
v___x_2720_ = l_Lean_Syntax_isOfKind(v___x_2718_, v___x_2719_);
if (v___x_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v___x_2722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_a_2707_);
return v___x_2722_;
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2723_ = l_Lean_Syntax_getArg(v___x_2718_, v___x_2712_);
lean_dec(v___x_2718_);
v___x_2724_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__9));
lean_inc(v___x_2723_);
v___x_2725_ = l_Lean_Syntax_isOfKind(v___x_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v___x_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v_a_2707_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
v___x_2728_ = l_Lean_Syntax_getArg(v___x_2723_, v___x_2717_);
lean_inc(v___x_2728_);
v___x_2729_ = l_Lean_Syntax_matchesNull(v___x_2728_, v___x_2712_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec(v___x_2728_);
lean_dec(v___x_2723_);
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
lean_ctor_set(v___x_2731_, 1, v_a_2707_);
return v___x_2731_;
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2732_ = l_Lean_Syntax_getArg(v___x_2728_, v___x_2717_);
lean_dec(v___x_2728_);
v___x_2733_ = ((lean_object*)(l_unexpandExists___closed__1));
lean_inc(v___x_2732_);
v___x_2734_ = l_Lean_Syntax_isOfKind(v___x_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; uint8_t v___x_2736_; 
v___x_2735_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2732_);
v___x_2736_ = l_Lean_Syntax_isOfKind(v___x_2732_, v___x_2735_);
if (v___x_2736_ == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2737_ = lean_box(0);
v___x_2738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_a_2707_);
return v___x_2738_;
}
else
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = l_Lean_Syntax_getArg(v___x_2723_, v___x_2712_);
v___x_2740_ = l_Lean_Syntax_matchesNull(v___x_2739_, v___x_2717_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2741_ = lean_box(0);
v___x_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
lean_ctor_set(v___x_2742_, 1, v_a_2707_);
return v___x_2742_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2743_ = lean_unsigned_to_nat(3u);
v___x_2744_ = l_Lean_Syntax_getArg(v___x_2723_, v___x_2743_);
lean_dec(v___x_2723_);
v___x_2745_ = l_Lean_SourceInfo_fromRef(v_a_2706_, v___x_2734_);
v___x_2746_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2747_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2745_, 4);
v___x_2748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2745_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2750_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_2751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2745_);
lean_ctor_set(v___x_2751_, 1, v___x_2749_);
lean_ctor_set(v___x_2751_, 2, v___x_2750_);
v___x_2752_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2745_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2745_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_Syntax_node6(v___x_2745_, v___x_2746_, v___x_2748_, v___x_2732_, v___x_2751_, v___x_2753_, v___x_2744_, v___x_2755_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2756_);
lean_ctor_set(v___x_2757_, 1, v_a_2707_);
return v___x_2757_;
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v___x_2758_ = l_Lean_Syntax_getArg(v___x_2732_, v___x_2717_);
v___x_2759_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
lean_inc(v___x_2758_);
v___x_2760_ = l_Lean_Syntax_isOfKind(v___x_2758_, v___x_2759_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v___x_2758_);
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2761_ = lean_box(0);
v___x_2762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_a_2707_);
return v___x_2762_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v___x_2763_ = l_Lean_Syntax_getArg(v___x_2758_, v___x_2712_);
lean_dec(v___x_2758_);
v___x_2764_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
lean_inc(v___x_2763_);
v___x_2765_ = l_Lean_Syntax_isOfKind(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v___x_2763_);
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2766_ = lean_box(0);
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_a_2707_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2768_ = l_Lean_Syntax_getArg(v___x_2763_, v___x_2717_);
lean_dec(v___x_2763_);
v___x_2769_ = lean_box(0);
v___x_2770_ = l_Lean_Syntax_matchesIdent(v___x_2768_, v___x_2769_);
lean_dec(v___x_2768_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2771_ = lean_box(0);
v___x_2772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
lean_ctor_set(v___x_2772_, 1, v_a_2707_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; 
v___x_2773_ = l_Lean_Syntax_getArg(v___x_2732_, v___x_2712_);
v___x_2774_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__14));
lean_inc(v___x_2773_);
v___x_2775_ = l_Lean_Syntax_isOfKind(v___x_2773_, v___x_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
lean_dec(v___x_2773_);
lean_dec(v___x_2732_);
lean_dec(v___x_2723_);
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
lean_ctor_set(v___x_2777_, 1, v_a_2707_);
return v___x_2777_;
}
else
{
lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v___x_2780_; 
v___x_2778_ = lean_unsigned_to_nat(3u);
v___x_2779_ = l_Lean_Syntax_getArg(v___x_2732_, v___x_2778_);
lean_dec(v___x_2732_);
lean_inc(v___x_2779_);
v___x_2780_ = l_Lean_Syntax_matchesNull(v___x_2779_, v___x_2712_);
if (v___x_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec(v___x_2779_);
lean_dec(v___x_2773_);
lean_dec(v___x_2723_);
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
lean_ctor_set(v___x_2782_, 1, v_a_2707_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2783_ = l_Lean_Syntax_getArg(v___x_2723_, v___x_2712_);
v___x_2784_ = l_Lean_Syntax_matchesNull(v___x_2783_, v___x_2717_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec(v___x_2779_);
lean_dec(v___x_2773_);
lean_dec(v___x_2723_);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
lean_ctor_set(v___x_2786_, 1, v_a_2707_);
return v___x_2786_;
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2787_ = l_Lean_Syntax_getArg(v___x_2779_, v___x_2717_);
lean_dec(v___x_2779_);
v___x_2788_ = l_Lean_Syntax_getArg(v___x_2723_, v___x_2778_);
lean_dec(v___x_2723_);
v___x_2789_ = 0;
v___x_2790_ = l_Lean_SourceInfo_fromRef(v_a_2706_, v___x_2789_);
v___x_2791_ = ((lean_object*)(l_unexpandSubtype___closed__1));
v___x_2792_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_2790_, 5);
v___x_2793_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2790_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
v___x_2794_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_2795_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_2796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2790_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l_Lean_Syntax_node2(v___x_2790_, v___x_2794_, v___x_2796_, v___x_2787_);
v___x_2798_ = ((lean_object*)(l_unexpandSubtype___closed__3));
v___x_2799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2790_);
lean_ctor_set(v___x_2799_, 1, v___x_2798_);
v___x_2800_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_2801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2790_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = l_Lean_Syntax_node6(v___x_2790_, v___x_2791_, v___x_2793_, v___x_2773_, v___x_2797_, v___x_2799_, v___x_2788_, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2802_);
lean_ctor_set(v___x_2803_, 1, v_a_2707_);
return v___x_2803_;
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
LEAN_EXPORT lean_object* l_unexpandSubtype___boxed(lean_object* v_x_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l_unexpandSubtype(v_x_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2805_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax(lean_object* v_x_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2811_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2808_);
v___x_2812_ = l_Lean_Syntax_isOfKind(v_x_2808_, v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec(v_x_2808_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
lean_ctor_set(v___x_2814_, 1, v_a_2810_);
return v___x_2814_;
}
else
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = lean_unsigned_to_nat(1u);
v___x_2816_ = l_Lean_Syntax_getArg(v_x_2808_, v___x_2815_);
lean_inc(v___x_2816_);
v___x_2817_ = l_Lean_Syntax_matchesNull(v___x_2816_, v___x_2815_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_dec(v___x_2816_);
lean_dec(v_x_2808_);
v___x_2818_ = lean_box(0);
v___x_2819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
lean_ctor_set(v___x_2819_, 1, v_a_2810_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
v___x_2820_ = lean_unsigned_to_nat(0u);
v___x_2821_ = l_Lean_Syntax_getArg(v___x_2816_, v___x_2820_);
lean_dec(v___x_2816_);
v___x_2822_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2821_);
v___x_2823_ = l_Lean_Syntax_isOfKind(v___x_2821_, v___x_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
lean_dec(v___x_2821_);
lean_dec(v_x_2808_);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v_a_2810_);
return v___x_2825_;
}
else
{
lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2826_ = l_Lean_Syntax_getArg(v___x_2821_, v___x_2815_);
lean_dec(v___x_2821_);
lean_inc(v___x_2826_);
v___x_2827_ = l_Lean_Syntax_matchesNull(v___x_2826_, v___x_2815_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
lean_dec(v___x_2826_);
lean_dec(v_x_2808_);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v_a_2810_);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; uint8_t v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2830_ = l_Lean_Syntax_getArg(v_x_2808_, v___x_2820_);
lean_dec(v_x_2808_);
v___x_2831_ = l_Lean_Syntax_getArg(v___x_2826_, v___x_2820_);
lean_dec(v___x_2826_);
v___x_2832_ = 0;
v___x_2833_ = l_Lean_SourceInfo_fromRef(v_a_2809_, v___x_2832_);
v___x_2834_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_2833_);
v___x_2835_ = l_Lean_Syntax_node1(v___x_2833_, v___x_2834_, v___x_2831_);
v___x_2836_ = l_Lean_Syntax_node2(v___x_2833_, v___x_2811_, v___x_2830_, v___x_2835_);
v___x_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2836_);
lean_ctor_set(v___x_2837_, 1, v_a_2810_);
return v___x_2837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntax___boxed(lean_object* v_x_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_unexpandTSyntax(v_x_2838_, v_a_2839_, v_a_2840_);
lean_dec(v_a_2839_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray(lean_object* v_x_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2842_);
v___x_2846_ = l_Lean_Syntax_isOfKind(v_x_2842_, v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v_x_2842_);
v___x_2847_ = lean_box(0);
v___x_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2847_);
lean_ctor_set(v___x_2848_, 1, v_a_2844_);
return v___x_2848_;
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2849_ = lean_unsigned_to_nat(1u);
v___x_2850_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2849_);
lean_inc(v___x_2850_);
v___x_2851_ = l_Lean_Syntax_matchesNull(v___x_2850_, v___x_2849_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec(v___x_2850_);
lean_dec(v_x_2842_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
lean_ctor_set(v___x_2853_, 1, v_a_2844_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; uint8_t v___x_2857_; 
v___x_2854_ = lean_unsigned_to_nat(0u);
v___x_2855_ = l_Lean_Syntax_getArg(v___x_2850_, v___x_2854_);
lean_dec(v___x_2850_);
v___x_2856_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2855_);
v___x_2857_ = l_Lean_Syntax_isOfKind(v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v___x_2855_);
lean_dec(v_x_2842_);
v___x_2858_ = lean_box(0);
v___x_2859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v_a_2844_);
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2860_ = l_Lean_Syntax_getArg(v___x_2855_, v___x_2849_);
lean_dec(v___x_2855_);
lean_inc(v___x_2860_);
v___x_2861_ = l_Lean_Syntax_matchesNull(v___x_2860_, v___x_2849_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec(v___x_2860_);
lean_dec(v_x_2842_);
v___x_2862_ = lean_box(0);
v___x_2863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
lean_ctor_set(v___x_2863_, 1, v_a_2844_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2864_ = l_Lean_Syntax_getArg(v_x_2842_, v___x_2854_);
lean_dec(v_x_2842_);
v___x_2865_ = l_Lean_Syntax_getArg(v___x_2860_, v___x_2854_);
lean_dec(v___x_2860_);
v___x_2866_ = 0;
v___x_2867_ = l_Lean_SourceInfo_fromRef(v_a_2843_, v___x_2866_);
v___x_2868_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_2867_);
v___x_2869_ = l_Lean_Syntax_node1(v___x_2867_, v___x_2868_, v___x_2865_);
v___x_2870_ = l_Lean_Syntax_node2(v___x_2867_, v___x_2845_, v___x_2864_, v___x_2869_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
lean_ctor_set(v___x_2871_, 1, v_a_2844_);
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSyntaxArray___boxed(lean_object* v_x_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_unexpandTSyntaxArray(v_x_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray(lean_object* v_x_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2876_);
v___x_2880_ = l_Lean_Syntax_isOfKind(v_x_2876_, v___x_2879_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec(v_x_2876_);
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
lean_ctor_set(v___x_2882_, 1, v_a_2878_);
return v___x_2882_;
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; 
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = l_Lean_Syntax_getArg(v_x_2876_, v___x_2883_);
v___x_2885_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2884_);
v___x_2886_ = l_Lean_Syntax_matchesNull(v___x_2884_, v___x_2885_);
if (v___x_2886_ == 0)
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_dec(v___x_2884_);
lean_dec(v_x_2876_);
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2887_);
lean_ctor_set(v___x_2888_, 1, v_a_2878_);
return v___x_2888_;
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = l_Lean_Syntax_getArg(v___x_2884_, v___x_2889_);
v___x_2891_ = ((lean_object*)(l_unexpandListNil___redArg___closed__1));
lean_inc(v___x_2890_);
v___x_2892_ = l_Lean_Syntax_isOfKind(v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
lean_dec(v___x_2890_);
lean_dec(v___x_2884_);
lean_dec(v_x_2876_);
v___x_2893_ = lean_box(0);
v___x_2894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
lean_ctor_set(v___x_2894_, 1, v_a_2878_);
return v___x_2894_;
}
else
{
lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2895_ = l_Lean_Syntax_getArg(v___x_2890_, v___x_2883_);
lean_dec(v___x_2890_);
lean_inc(v___x_2895_);
v___x_2896_ = l_Lean_Syntax_matchesNull(v___x_2895_, v___x_2883_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec(v___x_2895_);
lean_dec(v___x_2884_);
lean_dec(v_x_2876_);
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
lean_ctor_set(v___x_2898_, 1, v_a_2878_);
return v___x_2898_;
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2899_ = l_Lean_Syntax_getArg(v_x_2876_, v___x_2889_);
lean_dec(v_x_2876_);
v___x_2900_ = l_Lean_Syntax_getArg(v___x_2895_, v___x_2889_);
lean_dec(v___x_2895_);
v___x_2901_ = l_Lean_Syntax_getArg(v___x_2884_, v___x_2883_);
lean_dec(v___x_2884_);
v___x_2902_ = 0;
v___x_2903_ = l_Lean_SourceInfo_fromRef(v_a_2877_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_2903_);
v___x_2905_ = l_Lean_Syntax_node2(v___x_2903_, v___x_2904_, v___x_2900_, v___x_2901_);
v___x_2906_ = l_Lean_Syntax_node2(v___x_2903_, v___x_2879_, v___x_2899_, v___x_2905_);
v___x_2907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
lean_ctor_set(v___x_2907_, 1, v_a_2878_);
return v___x_2907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandTSepArray___boxed(lean_object* v_x_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_unexpandTSepArray(v_x_2908_, v_a_2909_, v_a_2910_);
lean_dec(v_a_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem(lean_object* v_x_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2915_);
v___x_2919_ = l_Lean_Syntax_isOfKind(v_x_2915_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v_x_2915_);
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v_a_2917_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2922_);
lean_dec(v_x_2915_);
v___x_2924_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_2923_);
v___x_2925_ = l_Lean_Syntax_matchesNull(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_a_2917_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v___x_2929_ = l_Lean_Syntax_getArg(v___x_2923_, v___x_2928_);
v___x_2930_ = l_Lean_Syntax_getArg(v___x_2923_, v___x_2922_);
lean_dec(v___x_2923_);
v___x_2931_ = 0;
v___x_2932_ = l_Lean_SourceInfo_fromRef(v_a_2916_, v___x_2931_);
v___x_2933_ = ((lean_object*)(l_unexpandGetElem___closed__1));
v___x_2934_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
lean_inc_n(v___x_2932_, 2);
v___x_2935_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2932_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2937_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2932_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
v___x_2938_ = l_Lean_Syntax_node4(v___x_2932_, v___x_2933_, v___x_2929_, v___x_2935_, v___x_2930_, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
lean_ctor_set(v___x_2939_, 1, v_a_2917_);
return v___x_2939_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem___boxed(lean_object* v_x_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_unexpandGetElem(v_x_2940_, v_a_2941_, v_a_2942_);
lean_dec(v_a_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21(lean_object* v_x_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2951_; uint8_t v___x_2952_; 
v___x_2951_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2948_);
v___x_2952_ = l_Lean_Syntax_isOfKind(v_x_2948_, v___x_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v_x_2948_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
lean_ctor_set(v___x_2954_, 1, v_a_2950_);
return v___x_2954_;
}
else
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v___x_2955_ = lean_unsigned_to_nat(1u);
v___x_2956_ = l_Lean_Syntax_getArg(v_x_2948_, v___x_2955_);
lean_dec(v_x_2948_);
v___x_2957_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2956_);
v___x_2958_ = l_Lean_Syntax_matchesNull(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
lean_dec(v___x_2956_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
lean_ctor_set(v___x_2960_, 1, v_a_2950_);
return v___x_2960_;
}
else
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2961_ = lean_unsigned_to_nat(0u);
v___x_2962_ = l_Lean_Syntax_getArg(v___x_2956_, v___x_2961_);
v___x_2963_ = l_Lean_Syntax_getArg(v___x_2956_, v___x_2955_);
lean_dec(v___x_2956_);
v___x_2964_ = 0;
v___x_2965_ = l_Lean_SourceInfo_fromRef(v_a_2949_, v___x_2964_);
v___x_2966_ = ((lean_object*)(l_unexpandGetElem_x21___closed__1));
v___x_2967_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_2968_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_2965_, 4);
v___x_2969_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2965_);
lean_ctor_set(v___x_2969_, 1, v___x_2967_);
lean_ctor_set(v___x_2969_, 2, v___x_2968_);
v___x_2970_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_2971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2965_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_2973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2965_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = ((lean_object*)(l_unexpandGetElem_x21___closed__2));
v___x_2975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2965_);
lean_ctor_set(v___x_2975_, 1, v___x_2974_);
lean_inc_ref(v___x_2969_);
v___x_2976_ = l_Lean_Syntax_node7(v___x_2965_, v___x_2966_, v___x_2962_, v___x_2969_, v___x_2971_, v___x_2963_, v___x_2973_, v___x_2969_, v___x_2975_);
v___x_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2977_, 0, v___x_2976_);
lean_ctor_set(v___x_2977_, 1, v_a_2950_);
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x21___boxed(lean_object* v_x_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_unexpandGetElem_x21(v_x_2978_, v_a_2979_, v_a_2980_);
lean_dec(v_a_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f(lean_object* v_x_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v___x_2989_; uint8_t v___x_2990_; 
v___x_2989_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_2986_);
v___x_2990_ = l_Lean_Syntax_isOfKind(v_x_2986_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec(v_x_2986_);
v___x_2991_ = lean_box(0);
v___x_2992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
lean_ctor_set(v___x_2992_, 1, v_a_2988_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v___x_2993_ = lean_unsigned_to_nat(1u);
v___x_2994_ = l_Lean_Syntax_getArg(v_x_2986_, v___x_2993_);
lean_dec(v_x_2986_);
v___x_2995_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2994_);
v___x_2996_ = l_Lean_Syntax_matchesNull(v___x_2994_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
lean_ctor_set(v___x_2998_, 1, v_a_2988_);
return v___x_2998_;
}
else
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_2999_ = lean_unsigned_to_nat(0u);
v___x_3000_ = l_Lean_Syntax_getArg(v___x_2994_, v___x_2999_);
v___x_3001_ = l_Lean_Syntax_getArg(v___x_2994_, v___x_2993_);
lean_dec(v___x_2994_);
v___x_3002_ = 0;
v___x_3003_ = l_Lean_SourceInfo_fromRef(v_a_2987_, v___x_3002_);
v___x_3004_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__1));
v___x_3005_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_3006_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
lean_inc_n(v___x_3003_, 4);
v___x_3007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3003_);
lean_ctor_set(v___x_3007_, 1, v___x_3005_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
v___x_3008_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_3009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3003_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3011_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3003_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = ((lean_object*)(l_unexpandGetElem_x3f___closed__2));
v___x_3013_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3003_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
lean_inc_ref(v___x_3007_);
v___x_3014_ = l_Lean_Syntax_node7(v___x_3003_, v___x_3004_, v___x_3000_, v___x_3007_, v___x_3009_, v___x_3001_, v___x_3011_, v___x_3007_, v___x_3013_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
lean_ctor_set(v___x_3015_, 1, v_a_2988_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandGetElem_x3f___boxed(lean_object* v_x_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_unexpandGetElem_x3f(v_x_3016_, v_a_3017_, v_a_3018_);
lean_dec(v_a_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg(lean_object* v_a_3020_, lean_object* v_a_3021_){
_start:
{
uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3022_ = 0;
v___x_3023_ = l_Lean_SourceInfo_fromRef(v_a_3020_, v___x_3022_);
v___x_3024_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3025_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3023_, 3);
v___x_3026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3023_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3028_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3029_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3023_);
lean_ctor_set(v___x_3029_, 1, v___x_3027_);
lean_ctor_set(v___x_3029_, 2, v___x_3028_);
v___x_3030_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3023_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
v___x_3032_ = l_Lean_Syntax_node3(v___x_3023_, v___x_3024_, v___x_3026_, v___x_3029_, v___x_3031_);
v___x_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3033_, 0, v___x_3032_);
lean_ctor_set(v___x_3033_, 1, v_a_3021_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___redArg___boxed(lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_unexpandArrayEmpty___redArg(v_a_3034_, v_a_3035_);
lean_dec(v_a_3034_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty(lean_object* v_x_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v___x_3040_; 
v___x_3040_ = l_unexpandArrayEmpty___redArg(v_a_3038_, v_a_3039_);
return v___x_3040_;
}
}
LEAN_EXPORT lean_object* l_unexpandArrayEmpty___boxed(lean_object* v_x_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_unexpandArrayEmpty(v_x_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3042_);
lean_dec(v_x_3041_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg(lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
uint8_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3047_ = 0;
v___x_3048_ = l_Lean_SourceInfo_fromRef(v_a_3045_, v___x_3047_);
v___x_3049_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3050_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3048_, 3);
v___x_3051_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3048_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3053_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3054_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3048_);
lean_ctor_set(v___x_3054_, 1, v___x_3052_);
lean_ctor_set(v___x_3054_, 2, v___x_3053_);
v___x_3055_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3048_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Lean_Syntax_node3(v___x_3048_, v___x_3049_, v___x_3051_, v___x_3054_, v___x_3056_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_ctor_set(v___x_3058_, 1, v_a_3046_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___redArg___boxed(lean_object* v_a_3059_, lean_object* v_a_3060_){
_start:
{
lean_object* v_res_3061_; 
v_res_3061_ = l_unexpandMkArray0___redArg(v_a_3059_, v_a_3060_);
lean_dec(v_a_3059_);
return v_res_3061_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0(lean_object* v_x_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_unexpandMkArray0___redArg(v_a_3063_, v_a_3064_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray0___boxed(lean_object* v_x_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_unexpandMkArray0(v_x_3066_, v_a_3067_, v_a_3068_);
lean_dec(v_a_3067_);
lean_dec(v_x_3066_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1(lean_object* v_x_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3073_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3070_);
v___x_3074_ = l_Lean_Syntax_isOfKind(v_x_3070_, v___x_3073_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
lean_dec(v_x_3070_);
v___x_3075_ = lean_box(0);
v___x_3076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v_a_3072_);
return v___x_3076_;
}
else
{
lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3077_ = lean_unsigned_to_nat(1u);
v___x_3078_ = l_Lean_Syntax_getArg(v_x_3070_, v___x_3077_);
lean_dec(v_x_3070_);
lean_inc(v___x_3078_);
v___x_3079_ = l_Lean_Syntax_matchesNull(v___x_3078_, v___x_3077_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v___x_3078_);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v_a_3072_);
return v___x_3081_;
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = l_Lean_Syntax_getArg(v___x_3078_, v___x_3082_);
lean_dec(v___x_3078_);
v___x_3084_ = 0;
v___x_3085_ = l_Lean_SourceInfo_fromRef(v_a_3071_, v___x_3084_);
v___x_3086_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3087_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3085_, 3);
v___x_3088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3085_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3090_ = l_Lean_Syntax_node1(v___x_3085_, v___x_3089_, v___x_3083_);
v___x_3091_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3085_);
lean_ctor_set(v___x_3092_, 1, v___x_3091_);
v___x_3093_ = l_Lean_Syntax_node3(v___x_3085_, v___x_3086_, v___x_3088_, v___x_3090_, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
lean_ctor_set(v___x_3094_, 1, v_a_3072_);
return v___x_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray1___boxed(lean_object* v_x_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_unexpandMkArray1(v_x_3095_, v_a_3096_, v_a_3097_);
lean_dec(v_a_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2(lean_object* v_x_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
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
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3112_ = lean_unsigned_to_nat(0u);
v___x_3113_ = l_Lean_Syntax_getArg(v___x_3107_, v___x_3112_);
v___x_3114_ = l_Lean_Syntax_getArg(v___x_3107_, v___x_3106_);
lean_dec(v___x_3107_);
v___x_3115_ = 0;
v___x_3116_ = l_Lean_SourceInfo_fromRef(v_a_3100_, v___x_3115_);
v___x_3117_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3118_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3116_, 4);
v___x_3119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3116_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3121_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3122_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3116_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v___x_3123_ = l_Lean_Syntax_node3(v___x_3116_, v___x_3120_, v___x_3113_, v___x_3122_, v___x_3114_);
v___x_3124_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3116_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
v___x_3126_ = l_Lean_Syntax_node3(v___x_3116_, v___x_3117_, v___x_3119_, v___x_3123_, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v_a_3101_);
return v___x_3127_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray2___boxed(lean_object* v_x_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_unexpandMkArray2(v_x_3128_, v_a_3129_, v_a_3130_);
lean_dec(v_a_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3(lean_object* v_x_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3132_);
v___x_3136_ = l_Lean_Syntax_isOfKind(v_x_3132_, v___x_3135_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
lean_dec(v_x_3132_);
v___x_3137_ = lean_box(0);
v___x_3138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
lean_ctor_set(v___x_3138_, 1, v_a_3134_);
return v___x_3138_;
}
else
{
lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v___x_3139_ = lean_unsigned_to_nat(1u);
v___x_3140_ = l_Lean_Syntax_getArg(v_x_3132_, v___x_3139_);
lean_dec(v_x_3132_);
v___x_3141_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_3140_);
v___x_3142_ = l_Lean_Syntax_matchesNull(v___x_3140_, v___x_3141_);
if (v___x_3142_ == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v_a_3134_);
return v___x_3144_;
}
else
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_3145_);
v___x_3147_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_3139_);
v___x_3148_ = lean_unsigned_to_nat(2u);
v___x_3149_ = l_Lean_Syntax_getArg(v___x_3140_, v___x_3148_);
lean_dec(v___x_3140_);
v___x_3150_ = 0;
v___x_3151_ = l_Lean_SourceInfo_fromRef(v_a_3133_, v___x_3150_);
v___x_3152_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3153_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3151_, 4);
v___x_3154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3151_);
lean_ctor_set(v___x_3154_, 1, v___x_3153_);
v___x_3155_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3156_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3151_);
lean_ctor_set(v___x_3157_, 1, v___x_3156_);
lean_inc_ref(v___x_3157_);
v___x_3158_ = l_Lean_Syntax_node5(v___x_3151_, v___x_3155_, v___x_3146_, v___x_3157_, v___x_3147_, v___x_3157_, v___x_3149_);
v___x_3159_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3151_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
v___x_3161_ = l_Lean_Syntax_node3(v___x_3151_, v___x_3152_, v___x_3154_, v___x_3158_, v___x_3160_);
v___x_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v_a_3134_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray3___boxed(lean_object* v_x_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_unexpandMkArray3(v_x_3163_, v_a_3164_, v_a_3165_);
lean_dec(v_a_3164_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4(lean_object* v_x_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_){
_start:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3167_);
v___x_3171_ = l_Lean_Syntax_isOfKind(v_x_3167_, v___x_3170_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v_x_3167_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v_a_3169_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v___x_3174_ = lean_unsigned_to_nat(1u);
v___x_3175_ = l_Lean_Syntax_getArg(v_x_3167_, v___x_3174_);
lean_dec(v_x_3167_);
v___x_3176_ = lean_unsigned_to_nat(4u);
lean_inc(v___x_3175_);
v___x_3177_ = l_Lean_Syntax_matchesNull(v___x_3175_, v___x_3176_);
if (v___x_3177_ == 0)
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_dec(v___x_3175_);
v___x_3178_ = lean_box(0);
v___x_3179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3178_);
lean_ctor_set(v___x_3179_, 1, v_a_3169_);
return v___x_3179_;
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = l_Lean_Syntax_getArg(v___x_3175_, v___x_3180_);
v___x_3182_ = l_Lean_Syntax_getArg(v___x_3175_, v___x_3174_);
v___x_3183_ = lean_unsigned_to_nat(2u);
v___x_3184_ = l_Lean_Syntax_getArg(v___x_3175_, v___x_3183_);
v___x_3185_ = lean_unsigned_to_nat(3u);
v___x_3186_ = l_Lean_Syntax_getArg(v___x_3175_, v___x_3185_);
lean_dec(v___x_3175_);
v___x_3187_ = 0;
v___x_3188_ = l_Lean_SourceInfo_fromRef(v_a_3168_, v___x_3187_);
v___x_3189_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3190_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3188_, 4);
v___x_3191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3188_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3193_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3188_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
lean_inc_ref_n(v___x_3194_, 2);
v___x_3195_ = l_Lean_Syntax_node7(v___x_3188_, v___x_3192_, v___x_3181_, v___x_3194_, v___x_3182_, v___x_3194_, v___x_3184_, v___x_3194_, v___x_3186_);
v___x_3196_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3188_);
lean_ctor_set(v___x_3197_, 1, v___x_3196_);
v___x_3198_ = l_Lean_Syntax_node3(v___x_3188_, v___x_3189_, v___x_3191_, v___x_3195_, v___x_3197_);
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
lean_ctor_set(v___x_3199_, 1, v_a_3169_);
return v___x_3199_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray4___boxed(lean_object* v_x_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_unexpandMkArray4(v_x_3200_, v_a_3201_, v_a_3202_);
lean_dec(v_a_3201_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5(lean_object* v_x_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
lean_object* v___x_3207_; uint8_t v___x_3208_; 
v___x_3207_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3204_);
v___x_3208_ = l_Lean_Syntax_isOfKind(v_x_3204_, v___x_3207_);
if (v___x_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec(v_x_3204_);
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
lean_ctor_set(v___x_3210_, 1, v_a_3206_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v___x_3211_ = lean_unsigned_to_nat(1u);
v___x_3212_ = l_Lean_Syntax_getArg(v_x_3204_, v___x_3211_);
lean_dec(v_x_3204_);
v___x_3213_ = lean_unsigned_to_nat(5u);
lean_inc(v___x_3212_);
v___x_3214_ = l_Lean_Syntax_matchesNull(v___x_3212_, v___x_3213_);
if (v___x_3214_ == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
lean_dec(v___x_3212_);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v_a_3206_);
return v___x_3216_;
}
else
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3217_ = lean_unsigned_to_nat(0u);
v___x_3218_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3217_);
v___x_3219_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3211_);
v___x_3220_ = lean_unsigned_to_nat(2u);
v___x_3221_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3220_);
v___x_3222_ = lean_unsigned_to_nat(3u);
v___x_3223_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3222_);
v___x_3224_ = lean_unsigned_to_nat(4u);
v___x_3225_ = l_Lean_Syntax_getArg(v___x_3212_, v___x_3224_);
lean_dec(v___x_3212_);
v___x_3226_ = 0;
v___x_3227_ = l_Lean_SourceInfo_fromRef(v_a_3205_, v___x_3226_);
v___x_3228_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3229_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3227_, 4);
v___x_3230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3232_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3227_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = lean_unsigned_to_nat(9u);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
v___x_3236_ = lean_array_push(v___x_3235_, v___x_3218_);
lean_inc_ref_n(v___x_3233_, 3);
v___x_3237_ = lean_array_push(v___x_3236_, v___x_3233_);
v___x_3238_ = lean_array_push(v___x_3237_, v___x_3219_);
v___x_3239_ = lean_array_push(v___x_3238_, v___x_3233_);
v___x_3240_ = lean_array_push(v___x_3239_, v___x_3221_);
v___x_3241_ = lean_array_push(v___x_3240_, v___x_3233_);
v___x_3242_ = lean_array_push(v___x_3241_, v___x_3223_);
v___x_3243_ = lean_array_push(v___x_3242_, v___x_3233_);
v___x_3244_ = lean_array_push(v___x_3243_, v___x_3225_);
v___x_3245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3227_);
lean_ctor_set(v___x_3245_, 1, v___x_3231_);
lean_ctor_set(v___x_3245_, 2, v___x_3244_);
v___x_3246_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3227_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_Syntax_node3(v___x_3227_, v___x_3228_, v___x_3230_, v___x_3245_, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
lean_ctor_set(v___x_3249_, 1, v_a_3206_);
return v___x_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray5___boxed(lean_object* v_x_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_unexpandMkArray5(v_x_3250_, v_a_3251_, v_a_3252_);
lean_dec(v_a_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6(lean_object* v_x_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3257_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3254_);
v___x_3258_ = l_Lean_Syntax_isOfKind(v_x_3254_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; 
lean_dec(v_x_3254_);
v___x_3259_ = lean_box(0);
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v_a_3256_);
return v___x_3260_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3261_ = lean_unsigned_to_nat(1u);
v___x_3262_ = l_Lean_Syntax_getArg(v_x_3254_, v___x_3261_);
lean_dec(v_x_3254_);
v___x_3263_ = lean_unsigned_to_nat(6u);
lean_inc(v___x_3262_);
v___x_3264_ = l_Lean_Syntax_matchesNull(v___x_3262_, v___x_3263_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v___x_3262_);
v___x_3265_ = lean_box(0);
v___x_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v_a_3256_);
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3267_);
v___x_3269_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3261_);
v___x_3270_ = lean_unsigned_to_nat(2u);
v___x_3271_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3270_);
v___x_3272_ = lean_unsigned_to_nat(3u);
v___x_3273_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3272_);
v___x_3274_ = lean_unsigned_to_nat(4u);
v___x_3275_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3274_);
v___x_3276_ = lean_unsigned_to_nat(5u);
v___x_3277_ = l_Lean_Syntax_getArg(v___x_3262_, v___x_3276_);
lean_dec(v___x_3262_);
v___x_3278_ = 0;
v___x_3279_ = l_Lean_SourceInfo_fromRef(v_a_3255_, v___x_3278_);
v___x_3280_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3281_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3279_, 4);
v___x_3282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3279_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3284_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3285_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3279_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = lean_unsigned_to_nat(11u);
v___x_3287_ = lean_mk_empty_array_with_capacity(v___x_3286_);
v___x_3288_ = lean_array_push(v___x_3287_, v___x_3268_);
lean_inc_ref_n(v___x_3285_, 4);
v___x_3289_ = lean_array_push(v___x_3288_, v___x_3285_);
v___x_3290_ = lean_array_push(v___x_3289_, v___x_3269_);
v___x_3291_ = lean_array_push(v___x_3290_, v___x_3285_);
v___x_3292_ = lean_array_push(v___x_3291_, v___x_3271_);
v___x_3293_ = lean_array_push(v___x_3292_, v___x_3285_);
v___x_3294_ = lean_array_push(v___x_3293_, v___x_3273_);
v___x_3295_ = lean_array_push(v___x_3294_, v___x_3285_);
v___x_3296_ = lean_array_push(v___x_3295_, v___x_3275_);
v___x_3297_ = lean_array_push(v___x_3296_, v___x_3285_);
v___x_3298_ = lean_array_push(v___x_3297_, v___x_3277_);
v___x_3299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3279_);
lean_ctor_set(v___x_3299_, 1, v___x_3283_);
lean_ctor_set(v___x_3299_, 2, v___x_3298_);
v___x_3300_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3279_);
lean_ctor_set(v___x_3301_, 1, v___x_3300_);
v___x_3302_ = l_Lean_Syntax_node3(v___x_3279_, v___x_3280_, v___x_3282_, v___x_3299_, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
lean_ctor_set(v___x_3303_, 1, v_a_3256_);
return v___x_3303_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray6___boxed(lean_object* v_x_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_unexpandMkArray6(v_x_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7(lean_object* v_x_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3308_);
v___x_3312_ = l_Lean_Syntax_isOfKind(v_x_3308_, v___x_3311_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
lean_dec(v_x_3308_);
v___x_3313_ = lean_box(0);
v___x_3314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v_a_3310_);
return v___x_3314_;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3315_ = lean_unsigned_to_nat(1u);
v___x_3316_ = l_Lean_Syntax_getArg(v_x_3308_, v___x_3315_);
lean_dec(v_x_3308_);
v___x_3317_ = lean_unsigned_to_nat(7u);
lean_inc(v___x_3316_);
v___x_3318_ = l_Lean_Syntax_matchesNull(v___x_3316_, v___x_3317_);
if (v___x_3318_ == 0)
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
lean_dec(v___x_3316_);
v___x_3319_ = lean_box(0);
v___x_3320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v_a_3310_);
return v___x_3320_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; uint8_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3321_ = lean_unsigned_to_nat(0u);
v___x_3322_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3321_);
v___x_3323_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3315_);
v___x_3324_ = lean_unsigned_to_nat(2u);
v___x_3325_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3324_);
v___x_3326_ = lean_unsigned_to_nat(3u);
v___x_3327_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3326_);
v___x_3328_ = lean_unsigned_to_nat(4u);
v___x_3329_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3328_);
v___x_3330_ = lean_unsigned_to_nat(5u);
v___x_3331_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3330_);
v___x_3332_ = lean_unsigned_to_nat(6u);
v___x_3333_ = l_Lean_Syntax_getArg(v___x_3316_, v___x_3332_);
lean_dec(v___x_3316_);
v___x_3334_ = 0;
v___x_3335_ = l_Lean_SourceInfo_fromRef(v_a_3309_, v___x_3334_);
v___x_3336_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3337_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3335_, 4);
v___x_3338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3335_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3340_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3335_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = lean_unsigned_to_nat(13u);
v___x_3343_ = lean_mk_empty_array_with_capacity(v___x_3342_);
v___x_3344_ = lean_array_push(v___x_3343_, v___x_3322_);
lean_inc_ref_n(v___x_3341_, 5);
v___x_3345_ = lean_array_push(v___x_3344_, v___x_3341_);
v___x_3346_ = lean_array_push(v___x_3345_, v___x_3323_);
v___x_3347_ = lean_array_push(v___x_3346_, v___x_3341_);
v___x_3348_ = lean_array_push(v___x_3347_, v___x_3325_);
v___x_3349_ = lean_array_push(v___x_3348_, v___x_3341_);
v___x_3350_ = lean_array_push(v___x_3349_, v___x_3327_);
v___x_3351_ = lean_array_push(v___x_3350_, v___x_3341_);
v___x_3352_ = lean_array_push(v___x_3351_, v___x_3329_);
v___x_3353_ = lean_array_push(v___x_3352_, v___x_3341_);
v___x_3354_ = lean_array_push(v___x_3353_, v___x_3331_);
v___x_3355_ = lean_array_push(v___x_3354_, v___x_3341_);
v___x_3356_ = lean_array_push(v___x_3355_, v___x_3333_);
v___x_3357_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3335_);
lean_ctor_set(v___x_3357_, 1, v___x_3339_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
v___x_3358_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3335_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_Syntax_node3(v___x_3335_, v___x_3336_, v___x_3338_, v___x_3357_, v___x_3359_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v_a_3310_);
return v___x_3361_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray7___boxed(lean_object* v_x_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_unexpandMkArray7(v_x_3362_, v_a_3363_, v_a_3364_);
lean_dec(v_a_3363_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8(lean_object* v_x_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_3366_);
v___x_3370_ = l_Lean_Syntax_isOfKind(v_x_3366_, v___x_3369_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec(v_x_3366_);
v___x_3371_ = lean_box(0);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v_a_3368_);
return v___x_3372_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; 
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = l_Lean_Syntax_getArg(v_x_3366_, v___x_3373_);
lean_dec(v_x_3366_);
v___x_3375_ = lean_unsigned_to_nat(8u);
lean_inc(v___x_3374_);
v___x_3376_ = l_Lean_Syntax_matchesNull(v___x_3374_, v___x_3375_);
if (v___x_3376_ == 0)
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec(v___x_3374_);
v___x_3377_ = lean_box(0);
v___x_3378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
lean_ctor_set(v___x_3378_, 1, v_a_3368_);
return v___x_3378_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; uint8_t v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; 
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3379_);
v___x_3381_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3373_);
v___x_3382_ = lean_unsigned_to_nat(2u);
v___x_3383_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3382_);
v___x_3384_ = lean_unsigned_to_nat(3u);
v___x_3385_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3384_);
v___x_3386_ = lean_unsigned_to_nat(4u);
v___x_3387_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3386_);
v___x_3388_ = lean_unsigned_to_nat(5u);
v___x_3389_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3388_);
v___x_3390_ = lean_unsigned_to_nat(6u);
v___x_3391_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3390_);
v___x_3392_ = lean_unsigned_to_nat(7u);
v___x_3393_ = l_Lean_Syntax_getArg(v___x_3374_, v___x_3392_);
lean_dec(v___x_3374_);
v___x_3394_ = 0;
v___x_3395_ = l_Lean_SourceInfo_fromRef(v_a_3367_, v___x_3394_);
v___x_3396_ = ((lean_object*)(l_unexpandListToArray___closed__1));
v___x_3397_ = ((lean_object*)(l_unexpandListToArray___closed__2));
lean_inc_n(v___x_3395_, 4);
v___x_3398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3395_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3400_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3395_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_unsigned_to_nat(15u);
v___x_3403_ = lean_mk_empty_array_with_capacity(v___x_3402_);
v___x_3404_ = lean_array_push(v___x_3403_, v___x_3380_);
lean_inc_ref_n(v___x_3401_, 6);
v___x_3405_ = lean_array_push(v___x_3404_, v___x_3401_);
v___x_3406_ = lean_array_push(v___x_3405_, v___x_3381_);
v___x_3407_ = lean_array_push(v___x_3406_, v___x_3401_);
v___x_3408_ = lean_array_push(v___x_3407_, v___x_3383_);
v___x_3409_ = lean_array_push(v___x_3408_, v___x_3401_);
v___x_3410_ = lean_array_push(v___x_3409_, v___x_3385_);
v___x_3411_ = lean_array_push(v___x_3410_, v___x_3401_);
v___x_3412_ = lean_array_push(v___x_3411_, v___x_3387_);
v___x_3413_ = lean_array_push(v___x_3412_, v___x_3401_);
v___x_3414_ = lean_array_push(v___x_3413_, v___x_3389_);
v___x_3415_ = lean_array_push(v___x_3414_, v___x_3401_);
v___x_3416_ = lean_array_push(v___x_3415_, v___x_3391_);
v___x_3417_ = lean_array_push(v___x_3416_, v___x_3401_);
v___x_3418_ = lean_array_push(v___x_3417_, v___x_3393_);
v___x_3419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3395_);
lean_ctor_set(v___x_3419_, 1, v___x_3399_);
lean_ctor_set(v___x_3419_, 2, v___x_3418_);
v___x_3420_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3395_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l_Lean_Syntax_node3(v___x_3395_, v___x_3396_, v___x_3398_, v___x_3419_, v___x_3421_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v_a_3368_);
return v___x_3423_;
}
}
}
}
LEAN_EXPORT lean_object* l_unexpandMkArray8___boxed(lean_object* v_x_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_unexpandMkArray8(v_x_3424_, v_a_3425_, v_a_3426_);
lean_dec(v_a_3425_);
return v_res_3427_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4(void){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3475_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3476_ = l_String_toRawSubstring_x27(v___x_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1(lean_object* v_x_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_){
_start:
{
lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3508_ = ((lean_object*)(l_tacticFunext_______00__closed__1));
lean_inc(v_x_3505_);
v___x_3509_ = l_Lean_Syntax_isOfKind(v_x_3505_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec(v_x_3505_);
v___x_3510_ = lean_box(1);
v___x_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
lean_ctor_set(v___x_3511_, 1, v_a_3507_);
return v___x_3511_;
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3512_ = lean_unsigned_to_nat(0u);
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = l_Lean_Syntax_getArg(v_x_3505_, v___x_3513_);
lean_dec(v_x_3505_);
lean_inc(v___x_3514_);
v___x_3515_ = l_Lean_Syntax_matchesNull(v___x_3514_, v___x_3512_);
if (v___x_3515_ == 0)
{
uint8_t v___x_3516_; 
lean_inc(v___x_3514_);
v___x_3516_ = l_Lean_Syntax_matchesNull(v___x_3514_, v___x_3513_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = l_Lean_Syntax_getNumArgs(v___x_3514_);
v___x_3518_ = lean_nat_dec_le(v___x_3513_, v___x_3517_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
lean_dec(v___x_3517_);
lean_dec(v___x_3514_);
v___x_3519_ = lean_box(1);
v___x_3520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v_a_3507_);
return v___x_3520_;
}
else
{
lean_object* v_quotContext_3521_; lean_object* v_currMacroScope_3522_; lean_object* v_ref_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_xs_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; 
v_quotContext_3521_ = lean_ctor_get(v_a_3506_, 1);
v_currMacroScope_3522_ = lean_ctor_get(v_a_3506_, 2);
v_ref_3523_ = lean_ctor_get(v_a_3506_, 5);
v___x_3524_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_3512_);
v___x_3525_ = l_Lean_Syntax_getArgs(v___x_3514_);
lean_dec(v___x_3514_);
v___x_3526_ = l_Array_extract___redArg(v___x_3525_, v___x_3513_, v___x_3517_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3528_ = lean_box(2);
v___x_3529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
lean_ctor_set(v___x_3529_, 1, v___x_3527_);
lean_ctor_set(v___x_3529_, 2, v___x_3526_);
v_xs_3530_ = l_Lean_Syntax_getArgs(v___x_3529_);
lean_dec_ref_known(v___x_3529_, 3);
v___x_3531_ = l_Lean_SourceInfo_fromRef(v_ref_3523_, v___x_3516_);
v___x_3532_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3533_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3534_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3531_, 11);
v___x_3535_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3531_);
lean_ctor_set(v___x_3535_, 1, v___x_3533_);
v___x_3536_ = ((lean_object*)(l_tacticFunext_______00__closed__2));
v___x_3537_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3538_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3522_);
lean_inc(v_quotContext_3521_);
v___x_3539_ = l_Lean_addMacroScope(v_quotContext_3521_, v___x_3538_, v_currMacroScope_3522_);
v___x_3540_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3541_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3531_);
lean_ctor_set(v___x_3541_, 1, v___x_3537_);
lean_ctor_set(v___x_3541_, 2, v___x_3539_);
lean_ctor_set(v___x_3541_, 3, v___x_3540_);
v___x_3542_ = l_Lean_Syntax_node2(v___x_3531_, v___x_3534_, v___x_3535_, v___x_3541_);
v___x_3543_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3531_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3546_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3531_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
v___x_3548_ = l_Lean_Syntax_node1(v___x_3531_, v___x_3527_, v___x_3524_);
v___x_3549_ = l_Lean_Syntax_node2(v___x_3531_, v___x_3546_, v___x_3547_, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3531_);
lean_ctor_set(v___x_3550_, 1, v___x_3536_);
v___x_3551_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3552_ = l_Array_append___redArg(v___x_3551_, v_xs_3530_);
lean_dec_ref(v_xs_3530_);
v___x_3553_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3531_);
lean_ctor_set(v___x_3553_, 1, v___x_3527_);
lean_ctor_set(v___x_3553_, 2, v___x_3552_);
v___x_3554_ = l_Lean_Syntax_node2(v___x_3531_, v___x_3508_, v___x_3550_, v___x_3553_);
lean_inc_ref(v___x_3544_);
v___x_3555_ = l_Lean_Syntax_node5(v___x_3531_, v___x_3527_, v___x_3542_, v___x_3544_, v___x_3549_, v___x_3544_, v___x_3554_);
v___x_3556_ = l_Lean_Syntax_node1(v___x_3531_, v___x_3532_, v___x_3555_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v_a_3507_);
return v___x_3557_;
}
}
else
{
lean_object* v_quotContext_3558_; lean_object* v_currMacroScope_3559_; lean_object* v_ref_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v_quotContext_3558_ = lean_ctor_get(v_a_3506_, 1);
v_currMacroScope_3559_ = lean_ctor_get(v_a_3506_, 2);
v_ref_3560_ = lean_ctor_get(v_a_3506_, 5);
v___x_3561_ = l_Lean_Syntax_getArg(v___x_3514_, v___x_3512_);
lean_dec(v___x_3514_);
v___x_3562_ = l_Lean_SourceInfo_fromRef(v_ref_3560_, v___x_3515_);
v___x_3563_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__1));
v___x_3564_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3565_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3566_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
lean_inc_n(v___x_3562_, 8);
v___x_3567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3562_);
lean_ctor_set(v___x_3567_, 1, v___x_3565_);
v___x_3568_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3569_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3559_);
lean_inc(v_quotContext_3558_);
v___x_3570_ = l_Lean_addMacroScope(v_quotContext_3558_, v___x_3569_, v_currMacroScope_3559_);
v___x_3571_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3572_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3562_);
lean_ctor_set(v___x_3572_, 1, v___x_3568_);
lean_ctor_set(v___x_3572_, 2, v___x_3570_);
lean_ctor_set(v___x_3572_, 3, v___x_3571_);
v___x_3573_ = l_Lean_Syntax_node2(v___x_3562_, v___x_3566_, v___x_3567_, v___x_3572_);
v___x_3574_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3575_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3562_);
lean_ctor_set(v___x_3575_, 1, v___x_3574_);
v___x_3576_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3577_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3578_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3562_);
lean_ctor_set(v___x_3578_, 1, v___x_3576_);
v___x_3579_ = l_Lean_Syntax_node1(v___x_3562_, v___x_3564_, v___x_3561_);
v___x_3580_ = l_Lean_Syntax_node2(v___x_3562_, v___x_3577_, v___x_3578_, v___x_3579_);
v___x_3581_ = l_Lean_Syntax_node3(v___x_3562_, v___x_3564_, v___x_3573_, v___x_3575_, v___x_3580_);
v___x_3582_ = l_Lean_Syntax_node1(v___x_3562_, v___x_3563_, v___x_3581_);
v___x_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v_a_3507_);
return v___x_3583_;
}
}
else
{
lean_object* v_quotContext_3584_; lean_object* v_currMacroScope_3585_; lean_object* v_ref_3586_; uint8_t v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec(v___x_3514_);
v_quotContext_3584_ = lean_ctor_get(v_a_3506_, 1);
v_currMacroScope_3585_ = lean_ctor_get(v_a_3506_, 2);
v_ref_3586_ = lean_ctor_get(v_a_3506_, 5);
v___x_3587_ = 0;
v___x_3588_ = l_Lean_SourceInfo_fromRef(v_ref_3586_, v___x_3587_);
v___x_3589_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__12));
v___x_3590_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__13));
lean_inc_n(v___x_3588_, 17);
v___x_3591_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3588_);
lean_ctor_set(v___x_3591_, 1, v___x_3590_);
v___x_3592_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_3593_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_3594_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3595_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_3596_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_3597_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3588_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
v___x_3598_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__2));
v___x_3599_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__3));
v___x_3600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3588_);
lean_ctor_set(v___x_3600_, 1, v___x_3598_);
v___x_3601_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4, &l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4_once, _init_l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__4);
v___x_3602_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__5));
lean_inc(v_currMacroScope_3585_);
lean_inc(v_quotContext_3584_);
v___x_3603_ = l_Lean_addMacroScope(v_quotContext_3584_, v___x_3602_, v_currMacroScope_3585_);
v___x_3604_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__7));
v___x_3605_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3588_);
lean_ctor_set(v___x_3605_, 1, v___x_3601_);
lean_ctor_set(v___x_3605_, 2, v___x_3603_);
lean_ctor_set(v___x_3605_, 3, v___x_3604_);
v___x_3606_ = l_Lean_Syntax_node2(v___x_3588_, v___x_3599_, v___x_3600_, v___x_3605_);
v___x_3607_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_3608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3588_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__9));
v___x_3610_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__10));
v___x_3611_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3588_);
lean_ctor_set(v___x_3611_, 1, v___x_3609_);
v___x_3612_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3588_);
lean_ctor_set(v___x_3613_, 1, v___x_3594_);
lean_ctor_set(v___x_3613_, 2, v___x_3612_);
v___x_3614_ = l_Lean_Syntax_node2(v___x_3588_, v___x_3610_, v___x_3611_, v___x_3613_);
v___x_3615_ = l_Lean_Syntax_node3(v___x_3588_, v___x_3594_, v___x_3606_, v___x_3608_, v___x_3614_);
v___x_3616_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3593_, v___x_3615_);
v___x_3617_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3592_, v___x_3616_);
v___x_3618_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_3619_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3588_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_Syntax_node3(v___x_3588_, v___x_3595_, v___x_3597_, v___x_3617_, v___x_3619_);
v___x_3621_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3594_, v___x_3620_);
v___x_3622_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3593_, v___x_3621_);
v___x_3623_ = l_Lean_Syntax_node1(v___x_3588_, v___x_3592_, v___x_3622_);
v___x_3624_ = l_Lean_Syntax_node2(v___x_3588_, v___x_3589_, v___x_3591_, v___x_3623_);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
lean_ctor_set(v___x_3625_, 1, v_a_3507_);
return v___x_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__tacticFunext________1___boxed(lean_object* v_x_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___aux__Init__NotationExtra______macroRules__tacticFunext________1(v_x_3626_, v_a_3627_, v_a_3628_);
lean_dec_ref(v_a_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(size_t v_sz_3630_, size_t v_i_3631_, lean_object* v_bs_3632_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_lt(v_i_3631_, v_sz_3630_);
if (v___x_3633_ == 0)
{
return v_bs_3632_;
}
else
{
lean_object* v_v_3634_; lean_object* v___x_3635_; lean_object* v_bs_x27_3636_; size_t v___x_3637_; size_t v___x_3638_; lean_object* v___x_3639_; 
v_v_3634_ = lean_array_uget(v_bs_3632_, v_i_3631_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v_bs_x27_3636_ = lean_array_uset(v_bs_3632_, v_i_3631_, v___x_3635_);
v___x_3637_ = ((size_t)1ULL);
v___x_3638_ = lean_usize_add(v_i_3631_, v___x_3637_);
v___x_3639_ = lean_array_uset(v_bs_x27_3636_, v_i_3631_, v_v_3634_);
v_i_3631_ = v___x_3638_;
v_bs_3632_ = v___x_3639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1___boxed(lean_object* v_sz_3641_, lean_object* v_i_3642_, lean_object* v_bs_3643_){
_start:
{
size_t v_sz_boxed_3644_; size_t v_i_boxed_3645_; lean_object* v_res_3646_; 
v_sz_boxed_3644_ = lean_unbox_usize(v_sz_3641_);
lean_dec(v_sz_3641_);
v_i_boxed_3645_ = lean_unbox_usize(v_i_3642_);
lean_dec(v_i_3642_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_boxed_3644_, v_i_boxed_3645_, v_bs_3643_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(size_t v_sz_3647_, size_t v_i_3648_, lean_object* v_bs_3649_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_usize_dec_lt(v_i_3648_, v_sz_3647_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_bs_3649_);
return v___x_3651_;
}
else
{
lean_object* v_v_3652_; lean_object* v___x_3653_; lean_object* v_bs_x27_3654_; size_t v___x_3655_; size_t v___x_3656_; lean_object* v___x_3657_; 
v_v_3652_ = lean_array_uget(v_bs_3649_, v_i_3648_);
v___x_3653_ = lean_unsigned_to_nat(0u);
v_bs_x27_3654_ = lean_array_uset(v_bs_3649_, v_i_3648_, v___x_3653_);
v___x_3655_ = ((size_t)1ULL);
v___x_3656_ = lean_usize_add(v_i_3648_, v___x_3655_);
v___x_3657_ = lean_array_uset(v_bs_x27_3654_, v_i_3648_, v_v_3652_);
v_i_3648_ = v___x_3656_;
v_bs_3649_ = v___x_3657_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0___boxed(lean_object* v_sz_3659_, lean_object* v_i_3660_, lean_object* v_bs_3661_){
_start:
{
size_t v_sz_boxed_3662_; size_t v_i_boxed_3663_; lean_object* v_res_3664_; 
v_sz_boxed_3662_ = lean_unbox_usize(v_sz_3659_);
lean_dec(v_sz_3659_);
v_i_boxed_3663_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_res_3664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_boxed_3662_, v_i_boxed_3663_, v_bs_3661_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(uint8_t v___x_3665_, lean_object* v_as_3666_, size_t v_i_3667_, size_t v_stop_3668_, lean_object* v_b_3669_){
_start:
{
lean_object* v___y_3671_; uint8_t v___x_3675_; 
v___x_3675_ = lean_usize_dec_eq(v_i_3667_, v_stop_3668_);
if (v___x_3675_ == 0)
{
lean_object* v_fst_3676_; uint8_t v___x_3677_; 
v_fst_3676_ = lean_ctor_get(v_b_3669_, 0);
v___x_3677_ = lean_unbox(v_fst_3676_);
if (v___x_3677_ == 0)
{
lean_object* v_snd_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3686_; 
v_snd_3678_ = lean_ctor_get(v_b_3669_, 1);
v_isSharedCheck_3686_ = !lean_is_exclusive(v_b_3669_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v_b_3669_, 0);
lean_dec(v_unused_3687_);
v___x_3680_ = v_b_3669_;
v_isShared_3681_ = v_isSharedCheck_3686_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_snd_3678_);
lean_dec(v_b_3669_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3686_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_box(v___x_3665_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3682_);
v___x_3684_ = v___x_3680_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_snd_3678_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
v___y_3671_ = v___x_3684_;
goto v___jp_3670_;
}
}
}
else
{
lean_object* v_snd_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3698_; 
v_snd_3688_ = lean_ctor_get(v_b_3669_, 1);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_b_3669_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; 
v_unused_3699_ = lean_ctor_get(v_b_3669_, 0);
lean_dec(v_unused_3699_);
v___x_3690_ = v_b_3669_;
v_isShared_3691_ = v_isSharedCheck_3698_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_snd_3688_);
lean_dec(v_b_3669_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3698_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3696_; 
v___x_3692_ = lean_array_uget_borrowed(v_as_3666_, v_i_3667_);
lean_inc(v___x_3692_);
v___x_3693_ = lean_array_push(v_snd_3688_, v___x_3692_);
v___x_3694_ = lean_box(v___x_3675_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 1, v___x_3693_);
lean_ctor_set(v___x_3690_, 0, v___x_3694_);
v___x_3696_ = v___x_3690_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3693_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
v___y_3671_ = v___x_3696_;
goto v___jp_3670_;
}
}
}
}
else
{
return v_b_3669_;
}
v___jp_3670_:
{
size_t v___x_3672_; size_t v___x_3673_; 
v___x_3672_ = ((size_t)1ULL);
v___x_3673_ = lean_usize_add(v_i_3667_, v___x_3672_);
v_i_3667_ = v___x_3673_;
v_b_3669_ = v___y_3671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3___boxed(lean_object* v___x_3700_, lean_object* v_as_3701_, lean_object* v_i_3702_, lean_object* v_stop_3703_, lean_object* v_b_3704_){
_start:
{
uint8_t v___x_5033__boxed_3705_; size_t v_i_boxed_3706_; size_t v_stop_boxed_3707_; lean_object* v_res_3708_; 
v___x_5033__boxed_3705_ = lean_unbox(v___x_3700_);
v_i_boxed_3706_ = lean_unbox_usize(v_i_3702_);
lean_dec(v_i_3702_);
v_stop_boxed_3707_ = lean_unbox_usize(v_stop_3703_);
lean_dec(v_stop_3703_);
v_res_3708_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_5033__boxed_3705_, v_as_3701_, v_i_boxed_3706_, v_stop_boxed_3707_, v_b_3704_);
lean_dec_ref(v_as_3701_);
return v_res_3708_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__0));
v___x_3711_ = l_String_toRawSubstring_x27(v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(lean_object* v_as_3728_, size_t v_i_3729_, size_t v_stop_3730_, lean_object* v_b_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_usize_dec_eq(v_i_3729_, v_stop_3730_);
if (v___x_3734_ == 0)
{
lean_object* v_quotContext_3735_; lean_object* v_currMacroScope_3736_; lean_object* v_ref_3737_; size_t v___x_3738_; size_t v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_quotContext_3735_ = lean_ctor_get(v___y_3732_, 1);
v_currMacroScope_3736_ = lean_ctor_get(v___y_3732_, 2);
v_ref_3737_ = lean_ctor_get(v___y_3732_, 5);
v___x_3738_ = ((size_t)1ULL);
v___x_3739_ = lean_usize_sub(v_i_3729_, v___x_3738_);
v___x_3740_ = lean_array_uget_borrowed(v_as_3728_, v___x_3739_);
v___x_3741_ = l_Lean_SourceInfo_fromRef(v_ref_3737_, v___x_3734_);
v___x_3742_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_3743_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__1);
v___x_3744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__4));
lean_inc(v_currMacroScope_3736_);
lean_inc(v_quotContext_3735_);
v___x_3745_ = l_Lean_addMacroScope(v_quotContext_3735_, v___x_3744_, v_currMacroScope_3736_);
v___x_3746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___closed__8));
lean_inc_n(v___x_3741_, 2);
v___x_3747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3741_);
lean_ctor_set(v___x_3747_, 1, v___x_3743_);
lean_ctor_set(v___x_3747_, 2, v___x_3745_);
lean_ctor_set(v___x_3747_, 3, v___x_3746_);
v___x_3748_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
lean_inc(v___x_3740_);
v___x_3749_ = l_Lean_Syntax_node2(v___x_3741_, v___x_3748_, v___x_3740_, v_b_3731_);
v___x_3750_ = l_Lean_Syntax_node2(v___x_3741_, v___x_3742_, v___x_3747_, v___x_3749_);
v_i_3729_ = v___x_3739_;
v_b_3731_ = v___x_3750_;
goto _start;
}
else
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3752_, 0, v_b_3731_);
lean_ctor_set(v___x_3752_, 1, v___y_3733_);
return v___x_3752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2___boxed(lean_object* v_as_3753_, lean_object* v_i_3754_, lean_object* v_stop_3755_, lean_object* v_b_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
size_t v_i_boxed_3759_; size_t v_stop_boxed_3760_; lean_object* v_res_3761_; 
v_i_boxed_3759_ = lean_unbox_usize(v_i_3754_);
lean_dec(v_i_3754_);
v_stop_boxed_3760_ = lean_unbox_usize(v_stop_3755_);
lean_dec(v_stop_3755_);
v_res_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_as_3753_, v_i_boxed_3759_, v_stop_boxed_3760_, v_b_3756_, v___y_3757_, v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_as_3753_);
return v_res_3761_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__12));
v___x_3797_ = l_String_toRawSubstring_x27(v___x_3796_);
return v___x_3797_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_3802_ = l_Lean_mkAtom(v___x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(lean_object* v_x_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_){
_start:
{
lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3806_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__1));
lean_inc(v_x_3803_);
v___x_3807_ = l_Lean_Syntax_isOfKind(v_x_3803_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; 
lean_dec(v_x_3803_);
v___x_3808_ = lean_box(1);
v___x_3809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v_a_3805_);
return v___x_3809_;
}
else
{
lean_object* v___x_3810_; lean_object* v___y_3812_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3810_ = lean_unsigned_to_nat(0u);
v___x_3896_ = lean_unsigned_to_nat(1u);
v___x_3897_ = l_Lean_Syntax_getArg(v_x_3803_, v___x_3896_);
v___x_3898_ = l_Lean_Syntax_getArgs(v___x_3897_);
lean_dec(v___x_3897_);
v___x_3899_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___x_3900_ = lean_array_get_size(v___x_3898_);
v___x_3901_ = lean_nat_dec_lt(v___x_3810_, v___x_3900_);
if (v___x_3901_ == 0)
{
lean_dec_ref(v___x_3898_);
v___y_3812_ = v___x_3899_;
goto v___jp_3811_;
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3903_; size_t v___x_3904_; size_t v___x_3905_; lean_object* v___x_3906_; lean_object* v_snd_3907_; 
v___x_3902_ = lean_box(v___x_3901_);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3899_);
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = lean_usize_of_nat(v___x_3900_);
v___x_3906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__3(v___x_3807_, v___x_3898_, v___x_3904_, v___x_3905_, v___x_3903_);
lean_dec_ref(v___x_3898_);
v_snd_3907_ = lean_ctor_get(v___x_3906_, 1);
lean_inc(v_snd_3907_);
lean_dec_ref(v___x_3906_);
v___y_3812_ = v_snd_3907_;
goto v___jp_3811_;
}
v___jp_3811_:
{
size_t v_sz_3813_; size_t v___x_3814_; lean_object* v___x_3815_; 
v_sz_3813_ = lean_array_size(v___y_3812_);
v___x_3814_ = ((size_t)0ULL);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__0(v_sz_3813_, v___x_3814_, v___y_3812_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_dec(v_x_3803_);
v___x_3816_ = lean_box(1);
v___x_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v_a_3805_);
return v___x_3817_;
}
else
{
lean_object* v_val_3818_; lean_object* v___x_3819_; lean_object* v_k_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_val_3818_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_val_3818_);
lean_dec_ref_known(v___x_3815_, 1);
v___x_3819_ = lean_unsigned_to_nat(3u);
v_k_3820_ = l_Lean_Syntax_getArg(v_x_3803_, v___x_3819_);
lean_dec(v_x_3803_);
v___x_3821_ = lean_array_get_size(v_val_3818_);
v___x_3822_ = lean_unsigned_to_nat(8u);
v___x_3823_ = lean_nat_dec_lt(v___x_3821_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v_m_3825_; lean_object* v_quotContext_3826_; lean_object* v_currMacroScope_3827_; lean_object* v_ref_3828_; lean_object* v_y_3829_; lean_object* v_z_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; size_t v_sz_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; size_t v_sz_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3824_ = lean_unsigned_to_nat(1u);
v_m_3825_ = lean_nat_shiftr(v___x_3821_, v___x_3824_);
v_quotContext_3826_ = lean_ctor_get(v_a_3804_, 1);
v_currMacroScope_3827_ = lean_ctor_get(v_a_3804_, 2);
v_ref_3828_ = lean_ctor_get(v_a_3804_, 5);
lean_inc(v_m_3825_);
v_y_3829_ = l_Array_extract___redArg(v_val_3818_, v_m_3825_, v___x_3821_);
v_z_3830_ = l_Array_extract___redArg(v_val_3818_, v___x_3810_, v_m_3825_);
lean_dec(v_val_3818_);
v___x_3831_ = l_Lean_SourceInfo_fromRef(v_ref_3828_, v___x_3823_);
v___x_3832_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__2));
v___x_3833_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__3));
lean_inc_n(v___x_3831_, 15);
v___x_3834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3831_);
lean_ctor_set(v___x_3834_, 1, v___x_3832_);
v___x_3835_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__5));
v___x_3836_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_3837_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_3838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3831_);
lean_ctor_set(v___x_3838_, 1, v___x_3836_);
lean_ctor_set(v___x_3838_, 2, v___x_3837_);
lean_inc_ref_n(v___x_3838_, 3);
v___x_3839_ = l_Lean_Syntax_node1(v___x_3831_, v___x_3835_, v___x_3838_);
v___x_3840_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__7));
v___x_3841_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__9));
v___x_3842_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__11));
v___x_3843_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__13);
v___x_3844_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__14));
lean_inc(v_currMacroScope_3827_);
lean_inc(v_quotContext_3826_);
v___x_3845_ = l_Lean_addMacroScope(v_quotContext_3826_, v___x_3844_, v_currMacroScope_3827_);
v___x_3846_ = lean_box(0);
v___x_3847_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3831_);
lean_ctor_set(v___x_3847_, 1, v___x_3843_);
lean_ctor_set(v___x_3847_, 2, v___x_3845_);
lean_ctor_set(v___x_3847_, 3, v___x_3846_);
lean_inc_ref(v___x_3847_);
v___x_3848_ = l_Lean_Syntax_node1(v___x_3831_, v___x_3842_, v___x_3847_);
v___x_3849_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__6));
v___x_3850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3831_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__15));
v___x_3852_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3831_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v_sz_3853_ = lean_array_size(v_y_3829_);
v___x_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_3853_, v___x_3814_, v_y_3829_);
v___x_3855_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_3856_ = l_Lean_mkSepArray(v___x_3854_, v___x_3855_);
lean_dec_ref(v___x_3854_);
v___x_3857_ = l_Array_append___redArg(v___x_3837_, v___x_3856_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3831_);
lean_ctor_set(v___x_3858_, 1, v___x_3836_);
lean_ctor_set(v___x_3858_, 2, v___x_3857_);
v___x_3859_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_3860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3831_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_3862_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3831_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
lean_inc_ref(v___x_3862_);
lean_inc_ref(v___x_3860_);
lean_inc_ref(v___x_3852_);
v___x_3863_ = l_Lean_Syntax_node5(v___x_3831_, v___x_3806_, v___x_3852_, v___x_3858_, v___x_3860_, v_k_3820_, v___x_3862_);
v___x_3864_ = l_Lean_Syntax_node5(v___x_3831_, v___x_3841_, v___x_3848_, v___x_3838_, v___x_3838_, v___x_3850_, v___x_3863_);
v___x_3865_ = l_Lean_Syntax_node1(v___x_3831_, v___x_3840_, v___x_3864_);
v_sz_3866_ = lean_array_size(v_z_3830_);
v___x_3867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__1(v_sz_3866_, v___x_3814_, v_z_3830_);
v___x_3868_ = l_Lean_mkSepArray(v___x_3867_, v___x_3855_);
lean_dec_ref(v___x_3867_);
v___x_3869_ = l_Array_append___redArg(v___x_3837_, v___x_3868_);
lean_dec_ref(v___x_3868_);
v___x_3870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3831_);
lean_ctor_set(v___x_3870_, 1, v___x_3836_);
lean_ctor_set(v___x_3870_, 2, v___x_3869_);
v___x_3871_ = l_Lean_Syntax_node5(v___x_3831_, v___x_3806_, v___x_3852_, v___x_3870_, v___x_3860_, v___x_3847_, v___x_3862_);
v___x_3872_ = l_Lean_Syntax_node5(v___x_3831_, v___x_3833_, v___x_3834_, v___x_3839_, v___x_3865_, v___x_3838_, v___x_3871_);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
lean_ctor_set(v___x_3873_, 1, v_a_3805_);
return v___x_3873_;
}
else
{
uint8_t v___x_3874_; 
v___x_3874_ = lean_nat_dec_lt(v___x_3810_, v___x_3821_);
if (v___x_3874_ == 0)
{
lean_object* v___x_3875_; 
lean_dec(v_val_3818_);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v_k_3820_);
lean_ctor_set(v___x_3875_, 1, v_a_3805_);
return v___x_3875_;
}
else
{
size_t v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_usize_of_nat(v___x_3821_);
v___x_3877_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1_spec__2(v_val_3818_, v___x_3876_, v___x_3814_, v_k_3820_, v_a_3804_, v_a_3805_);
lean_dec(v_val_3818_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_a_3879_ = lean_ctor_get(v___x_3877_, 1);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3877_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3878_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
v_a_3887_ = lean_ctor_get(v___x_3877_, 0);
v_a_3888_ = lean_ctor_get(v___x_3877_, 1);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3877_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_inc(v_a_3887_);
lean_dec(v___x_3877_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3887_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
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
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___boxed(lean_object* v_x_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_){
_start:
{
lean_object* v_res_3911_; 
v_res_3911_ = l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1(v_x_3908_, v_a_3909_, v_a_3910_);
lean_dec_ref(v_a_3909_);
return v_res_3911_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0___closed__1));
v___x_4002_ = l_Lean_Name_append(v_x_4000_, v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(lean_object* v___x_4009_, size_t v_sz_4010_, size_t v_i_4011_, lean_object* v_bs_4012_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_lt(v_i_4011_, v_sz_4010_);
if (v___x_4013_ == 0)
{
lean_dec(v___x_4009_);
return v_bs_4012_;
}
else
{
lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_v_4016_; lean_object* v___x_4017_; lean_object* v_bs_x27_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; size_t v___x_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v___x_4014_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4015_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_v_4016_ = lean_array_uget(v_bs_4012_, v_i_4011_);
v___x_4017_ = lean_unsigned_to_nat(0u);
v_bs_x27_4018_ = lean_array_uset(v_bs_4012_, v_i_4011_, v___x_4017_);
v___x_4019_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___closed__1));
lean_inc_n(v___x_4009_, 2);
v___x_4020_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4009_);
lean_ctor_set(v___x_4020_, 1, v___x_4014_);
lean_ctor_set(v___x_4020_, 2, v___x_4015_);
v___x_4021_ = l_Lean_Syntax_node2(v___x_4009_, v___x_4019_, v___x_4020_, v_v_4016_);
v___x_4022_ = ((size_t)1ULL);
v___x_4023_ = lean_usize_add(v_i_4011_, v___x_4022_);
v___x_4024_ = lean_array_uset(v_bs_x27_4018_, v_i_4011_, v___x_4021_);
v_i_4011_ = v___x_4023_;
v_bs_4012_ = v___x_4024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1___boxed(lean_object* v___x_4026_, lean_object* v_sz_4027_, lean_object* v_i_4028_, lean_object* v_bs_4029_){
_start:
{
size_t v_sz_boxed_4030_; size_t v_i_boxed_4031_; lean_object* v_res_4032_; 
v_sz_boxed_4030_ = lean_unbox_usize(v_sz_4027_);
lean_dec(v_sz_4027_);
v_i_boxed_4031_ = lean_unbox_usize(v_i_4028_);
lean_dec(v_i_4028_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___x_4026_, v_sz_boxed_4030_, v_i_boxed_4031_, v_bs_4029_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(size_t v_sz_4033_, size_t v_i_4034_, lean_object* v_bs_4035_){
_start:
{
uint8_t v___x_4036_; 
v___x_4036_ = lean_usize_dec_lt(v_i_4034_, v_sz_4033_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; 
v___x_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4037_, 0, v_bs_4035_);
return v___x_4037_;
}
else
{
lean_object* v_v_4038_; lean_object* v___x_4039_; uint8_t v___x_4040_; 
v_v_4038_ = lean_array_uget(v_bs_4035_, v_i_4034_);
v___x_4039_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4038_);
v___x_4040_ = l_Lean_Syntax_isOfKind(v_v_4038_, v___x_4039_);
if (v___x_4040_ == 0)
{
lean_object* v___x_4041_; 
lean_dec(v_v_4038_);
lean_dec_ref(v_bs_4035_);
v___x_4041_ = lean_box(0);
return v___x_4041_;
}
else
{
lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_bs_x27_4044_; lean_object* v_parents_4045_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4042_ = lean_unsigned_to_nat(0u);
v___x_4043_ = lean_unsigned_to_nat(1u);
v_bs_x27_4044_ = lean_array_uset(v_bs_4035_, v_i_4034_, v___x_4042_);
v_parents_4045_ = l_Lean_Syntax_getArg(v_v_4038_, v___x_4042_);
v___x_4051_ = l_Lean_Syntax_getArg(v_v_4038_, v___x_4043_);
lean_dec(v_v_4038_);
v___x_4052_ = l_Lean_Syntax_isNone(v___x_4051_);
if (v___x_4052_ == 0)
{
uint8_t v___x_4053_; 
v___x_4053_ = l_Lean_Syntax_matchesNull(v___x_4051_, v___x_4043_);
if (v___x_4053_ == 0)
{
lean_object* v___x_4054_; 
lean_dec(v_parents_4045_);
lean_dec_ref(v_bs_x27_4044_);
v___x_4054_ = lean_box(0);
return v___x_4054_;
}
else
{
goto v___jp_4046_;
}
}
else
{
lean_dec(v___x_4051_);
goto v___jp_4046_;
}
v___jp_4046_:
{
size_t v___x_4047_; size_t v___x_4048_; lean_object* v___x_4049_; 
v___x_4047_ = ((size_t)1ULL);
v___x_4048_ = lean_usize_add(v_i_4034_, v___x_4047_);
v___x_4049_ = lean_array_uset(v_bs_x27_4044_, v_i_4034_, v_parents_4045_);
v_i_4034_ = v___x_4048_;
v_bs_4035_ = v___x_4049_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0___boxed(lean_object* v_sz_4055_, lean_object* v_i_4056_, lean_object* v_bs_4057_){
_start:
{
size_t v_sz_boxed_4058_; size_t v_i_boxed_4059_; lean_object* v_res_4060_; 
v_sz_boxed_4058_ = lean_unbox_usize(v_sz_4055_);
lean_dec(v_sz_4055_);
v_i_boxed_4059_ = lean_unbox_usize(v_i_4056_);
lean_dec(v_i_4056_);
v_res_4060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_boxed_4058_, v_i_boxed_4059_, v_bs_4057_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(lean_object* v_x_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_){
_start:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; uint8_t v___x_4119_; 
v___x_4116_ = ((lean_object*)(l_Lean_unbracketedExplicitBinders___closed__1));
v___x_4117_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__0));
v___x_4118_ = ((lean_object*)(l_Lean_Parser_Command_classAbbrev___closed__1));
lean_inc(v_x_4113_);
v___x_4119_ = l_Lean_Syntax_isOfKind(v_x_4113_, v___x_4118_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
lean_dec(v_x_4113_);
v___x_4120_ = lean_box(1);
v___x_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v_a_4115_);
return v___x_4121_;
}
else
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; uint8_t v___x_4125_; 
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4122_);
v___x_4124_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__0));
lean_inc(v___x_4123_);
v___x_4125_ = l_Lean_Syntax_isOfKind(v___x_4123_, v___x_4124_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
lean_dec(v___x_4123_);
lean_dec(v_x_4113_);
v___x_4126_ = lean_box(1);
v___x_4127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4126_);
lean_ctor_set(v___x_4127_, 1, v_a_4115_);
return v___x_4127_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; size_t v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v___y_4189_; size_t v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v_ty_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; 
v___x_4128_ = lean_unsigned_to_nat(3u);
v___x_4129_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4128_);
v___x_4222_ = lean_unsigned_to_nat(4u);
v___x_4223_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4222_);
v___x_4257_ = lean_unsigned_to_nat(5u);
v___x_4258_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4257_);
v___x_4259_ = l_Lean_Syntax_isNone(v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4260_; uint8_t v___x_4261_; 
v___x_4260_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4258_);
v___x_4261_ = l_Lean_Syntax_matchesNull(v___x_4258_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
lean_dec(v___x_4258_);
lean_dec(v___x_4223_);
lean_dec(v___x_4129_);
lean_dec(v___x_4123_);
lean_dec(v_x_4113_);
v___x_4262_ = lean_box(1);
v___x_4263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4262_);
lean_ctor_set(v___x_4263_, 1, v_a_4115_);
return v___x_4263_;
}
else
{
lean_object* v___x_4264_; lean_object* v_ty_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_unsigned_to_nat(1u);
v_ty_4265_ = l_Lean_Syntax_getArg(v___x_4258_, v___x_4264_);
lean_dec(v___x_4258_);
v___x_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4266_, 0, v_ty_4265_);
v_ty_4225_ = v___x_4266_;
v___y_4226_ = v_a_4114_;
v___y_4227_ = v_a_4115_;
goto v___jp_4224_;
}
}
else
{
lean_object* v___x_4267_; 
lean_dec(v___x_4258_);
v___x_4267_ = lean_box(0);
v_ty_4225_ = v___x_4267_;
v___y_4226_ = v_a_4114_;
v___y_4227_ = v_a_4115_;
goto v___jp_4224_;
}
v___jp_4130_:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; size_t v_sz_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_inc_ref_n(v___y_4132_, 2);
v___x_4145_ = l_Array_append___redArg(v___y_4132_, v___y_4144_);
lean_dec_ref(v___y_4144_);
lean_inc_n(v___y_4140_, 7);
lean_inc_n(v___y_4143_, 21);
v___x_4146_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4146_, 0, v___y_4143_);
lean_ctor_set(v___x_4146_, 1, v___y_4140_);
lean_ctor_set(v___x_4146_, 2, v___x_4145_);
lean_inc(v___y_4139_);
v___x_4147_ = l_Lean_Syntax_node2(v___y_4143_, v___y_4139_, v___y_4131_, v___x_4146_);
v___x_4148_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__1));
v___x_4149_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__2));
v___x_4150_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___y_4143_);
lean_ctor_set(v___x_4150_, 1, v___x_4148_);
v_sz_4151_ = lean_array_size(v___y_4134_);
v___x_4152_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__1(v___y_4143_, v_sz_4151_, v___y_4142_, v___y_4134_);
v___x_4153_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16, &l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16_once, _init_l___aux__Init__NotationExtra______macroRules__term_x25_x5b___x7c___x5d__1___closed__16);
v___x_4154_ = l_Lean_mkSepArray(v___x_4152_, v___x_4153_);
lean_dec_ref(v___x_4152_);
v___x_4155_ = l_Array_append___redArg(v___y_4132_, v___x_4154_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4156_, 0, v___y_4143_);
lean_ctor_set(v___x_4156_, 1, v___y_4140_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4157_, 0, v___y_4143_);
lean_ctor_set(v___x_4157_, 1, v___y_4140_);
lean_ctor_set(v___x_4157_, 2, v___y_4132_);
lean_inc_ref_n(v___x_4157_, 4);
v___x_4158_ = l_Lean_Syntax_node3(v___y_4143_, v___x_4149_, v___x_4150_, v___x_4156_, v___x_4157_);
v___x_4159_ = l_Lean_Syntax_node1(v___y_4143_, v___y_4140_, v___x_4158_);
v___x_4160_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__4));
v___x_4161_ = l_Lean_Syntax_node1(v___y_4143_, v___x_4160_, v___x_4157_);
lean_inc(v___y_4133_);
v___x_4162_ = l_Lean_Syntax_node6(v___y_4143_, v___y_4133_, v___y_4136_, v___x_4129_, v___x_4147_, v___x_4159_, v___x_4157_, v___x_4161_);
lean_inc(v___y_4135_);
v___x_4163_ = l_Lean_Syntax_node2(v___y_4143_, v___y_4135_, v___x_4123_, v___x_4162_);
v___x_4164_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__5));
v___x_4165_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__6));
v___x_4166_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___y_4143_);
lean_ctor_set(v___x_4166_, 1, v___x_4164_);
v___x_4167_ = ((lean_object*)(l_unexpandListNil___redArg___closed__2));
v___x_4168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___y_4143_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__11));
lean_inc_ref_n(v___y_4138_, 2);
v___x_4170_ = l_Lean_Name_mkStr4(v___x_4116_, v___x_4117_, v___y_4138_, v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__6));
v___x_4172_ = l_Lean_Name_mkStr4(v___x_4116_, v___x_4117_, v___y_4138_, v___x_4171_);
v___x_4173_ = l_Lean_Syntax_node1(v___y_4143_, v___x_4172_, v___x_4157_);
v___x_4174_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__7));
v___x_4175_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__8));
v___x_4176_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___y_4143_);
lean_ctor_set(v___x_4176_, 1, v___x_4174_);
v___x_4177_ = l_Lean_Syntax_node2(v___y_4143_, v___x_4175_, v___x_4176_, v___x_4157_);
v___x_4178_ = l_Lean_Syntax_node2(v___y_4143_, v___x_4170_, v___x_4173_, v___x_4177_);
v___x_4179_ = l_Lean_Syntax_node1(v___y_4143_, v___y_4140_, v___x_4178_);
v___x_4180_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__21));
v___x_4181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___y_4143_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_Syntax_node1(v___y_4143_, v___y_4140_, v___y_4137_);
v___x_4183_ = l_Lean_Syntax_node5(v___y_4143_, v___x_4165_, v___x_4166_, v___x_4168_, v___x_4179_, v___x_4181_, v___x_4182_);
v___x_4184_ = l_Lean_Syntax_node2(v___y_4143_, v___y_4140_, v___x_4163_, v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___y_4141_);
return v___x_4185_;
}
v___jp_4186_:
{
lean_object* v_ref_4195_; uint8_t v___x_4196_; lean_object* v_ctor_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; size_t v_sz_4208_; lean_object* v___x_4209_; size_t v_sz_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; 
v_ref_4195_ = lean_ctor_get(v___y_4188_, 5);
v___x_4196_ = 0;
v_ctor_4197_ = l_Lean_mkIdentFrom(v___x_4129_, v___y_4194_, v___x_4196_);
v___x_4198_ = l_Lean_SourceInfo_fromRef(v_ref_4195_, v___x_4196_);
v___x_4199_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4200_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__9));
v___x_4201_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__11));
v___x_4202_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__13));
v___x_4203_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__14));
lean_inc_n(v___x_4198_, 3);
v___x_4204_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4198_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l_Lean_Syntax_node1(v___x_4198_, v___x_4202_, v___x_4204_);
v___x_4206_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___closed__15));
v___x_4207_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4208_ = lean_array_size(v___y_4191_);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__4(v_sz_4208_, v___y_4190_, v___y_4191_);
v_sz_4210_ = lean_array_size(v___x_4209_);
v___x_4211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1_spec__5(v_sz_4210_, v___y_4190_, v___x_4209_);
v___x_4212_ = l_Array_append___redArg(v___x_4207_, v___x_4211_);
lean_dec_ref(v___x_4211_);
v___x_4213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4198_);
lean_ctor_set(v___x_4213_, 1, v___x_4199_);
lean_ctor_set(v___x_4213_, 2, v___x_4212_);
if (lean_obj_tag(v___y_4192_) == 1)
{
lean_object* v_val_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v_val_4214_ = lean_ctor_get(v___y_4192_, 0);
lean_inc(v_val_4214_);
lean_dec_ref_known(v___y_4192_, 1);
v___x_4215_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__15));
lean_inc_ref(v___y_4193_);
v___x_4216_ = l_Lean_Name_mkStr4(v___x_4116_, v___x_4117_, v___y_4193_, v___x_4215_);
v___x_4217_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
lean_inc_n(v___x_4198_, 2);
v___x_4218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4198_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l_Lean_Syntax_node2(v___x_4198_, v___x_4216_, v___x_4218_, v_val_4214_);
v___x_4220_ = l_Array_mkArray1___redArg(v___x_4219_);
v___y_4131_ = v___x_4213_;
v___y_4132_ = v___x_4207_;
v___y_4133_ = v___x_4201_;
v___y_4134_ = v___y_4189_;
v___y_4135_ = v___x_4200_;
v___y_4136_ = v___x_4205_;
v___y_4137_ = v_ctor_4197_;
v___y_4138_ = v___y_4193_;
v___y_4139_ = v___x_4206_;
v___y_4140_ = v___x_4199_;
v___y_4141_ = v___y_4187_;
v___y_4142_ = v___y_4190_;
v___y_4143_ = v___x_4198_;
v___y_4144_ = v___x_4220_;
goto v___jp_4130_;
}
else
{
lean_object* v___x_4221_; 
lean_dec(v___y_4192_);
v___x_4221_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__33));
v___y_4131_ = v___x_4213_;
v___y_4132_ = v___x_4207_;
v___y_4133_ = v___x_4201_;
v___y_4134_ = v___y_4189_;
v___y_4135_ = v___x_4200_;
v___y_4136_ = v___x_4205_;
v___y_4137_ = v_ctor_4197_;
v___y_4138_ = v___y_4193_;
v___y_4139_ = v___x_4206_;
v___y_4140_ = v___x_4199_;
v___y_4141_ = v___y_4187_;
v___y_4142_ = v___y_4190_;
v___y_4143_ = v___x_4198_;
v___y_4144_ = v___x_4221_;
goto v___jp_4130_;
}
}
v___jp_4224_:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; size_t v_sz_4231_; size_t v___x_4232_; lean_object* v___x_4233_; 
v___x_4228_ = lean_unsigned_to_nat(7u);
v___x_4229_ = l_Lean_Syntax_getArg(v_x_4113_, v___x_4228_);
lean_dec(v_x_4113_);
v___x_4230_ = l_Lean_Syntax_getArgs(v___x_4229_);
lean_dec(v___x_4229_);
v_sz_4231_ = lean_array_size(v___x_4230_);
v___x_4232_ = ((size_t)0ULL);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1_spec__0(v_sz_4231_, v___x_4232_, v___x_4230_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
lean_dec(v_ty_4225_);
lean_dec(v___x_4223_);
lean_dec(v___x_4129_);
lean_dec(v___x_4123_);
v___x_4234_ = lean_box(1);
v___x_4235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4234_);
lean_ctor_set(v___x_4235_, 1, v___y_4227_);
return v___x_4235_;
}
else
{
lean_object* v_val_4236_; lean_object* v___x_4237_; lean_object* v_params_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v_val_4236_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_val_4236_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4237_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__1));
v_params_4238_ = l_Lean_Syntax_getArgs(v___x_4223_);
lean_dec(v___x_4223_);
v___x_4239_ = l_Lean_Syntax_getArg(v___x_4129_, v___x_4122_);
v___x_4240_ = l_Lean_Syntax_getId(v___x_4239_);
lean_dec(v___x_4239_);
v___x_4241_ = l_Lean_Name_hasMacroScopes(v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
v___x_4242_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v___x_4240_);
v___y_4187_ = v___y_4227_;
v___y_4188_ = v___y_4226_;
v___y_4189_ = v_val_4236_;
v___y_4190_ = v___x_4232_;
v___y_4191_ = v_params_4238_;
v___y_4192_ = v_ty_4225_;
v___y_4193_ = v___x_4237_;
v___y_4194_ = v___x_4242_;
goto v___jp_4186_;
}
else
{
lean_object* v_view_4243_; lean_object* v_name_4244_; lean_object* v_imported_4245_; lean_object* v_ctx_4246_; lean_object* v_scopes_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4256_; 
v_view_4243_ = l_Lean_extractMacroScopes(v___x_4240_);
v_name_4244_ = lean_ctor_get(v_view_4243_, 0);
v_imported_4245_ = lean_ctor_get(v_view_4243_, 1);
v_ctx_4246_ = lean_ctor_get(v_view_4243_, 2);
v_scopes_4247_ = lean_ctor_get(v_view_4243_, 3);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_view_4243_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4249_ = v_view_4243_;
v_isShared_4250_ = v_isSharedCheck_4256_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_scopes_4247_);
lean_inc(v_ctx_4246_);
lean_inc(v_imported_4245_);
lean_inc(v_name_4244_);
lean_dec(v_view_4243_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4256_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4251_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___lam__0(v_name_4244_);
if (v_isShared_4250_ == 0)
{
lean_ctor_set(v___x_4249_, 0, v___x_4251_);
v___x_4253_ = v___x_4249_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v___x_4251_);
lean_ctor_set(v_reuseFailAlloc_4255_, 1, v_imported_4245_);
lean_ctor_set(v_reuseFailAlloc_4255_, 2, v_ctx_4246_);
lean_ctor_set(v_reuseFailAlloc_4255_, 3, v_scopes_4247_);
v___x_4253_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
lean_object* v___x_4254_; 
v___x_4254_ = l_Lean_MacroScopesView_review(v___x_4253_);
v___y_4187_ = v___y_4227_;
v___y_4188_ = v___y_4226_;
v___y_4189_ = v_val_4236_;
v___y_4190_ = v___x_4232_;
v___y_4191_ = v_params_4238_;
v___y_4192_ = v_ty_4225_;
v___y_4193_ = v___x_4237_;
v___y_4194_ = v___x_4254_;
goto v___jp_4186_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1___boxed(lean_object* v_x_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l___aux__Init__NotationExtra______macroRules__Lean__Parser__Command__classAbbrev__1(v_x_4268_, v_a_4269_, v_a_4270_);
lean_dec_ref(v_a_4269_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(size_t v_sz_4356_, size_t v_i_4357_, lean_object* v_bs_4358_){
_start:
{
uint8_t v___x_4359_; 
v___x_4359_ = lean_usize_dec_lt(v_i_4357_, v_sz_4356_);
if (v___x_4359_ == 0)
{
lean_object* v___x_4360_; 
v___x_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4360_, 0, v_bs_4358_);
return v___x_4360_;
}
else
{
lean_object* v_v_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; 
v_v_4361_ = lean_array_uget(v_bs_4358_, v_i_4357_);
v___x_4362_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
lean_inc(v_v_4361_);
v___x_4363_ = l_Lean_Syntax_isOfKind(v_v_4361_, v___x_4362_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; 
lean_dec(v_v_4361_);
lean_dec_ref(v_bs_4358_);
v___x_4364_ = lean_box(0);
return v___x_4364_;
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v_bs_x27_4367_; lean_object* v_ts_4368_; size_t v___x_4369_; size_t v___x_4370_; lean_object* v___x_4371_; 
v___x_4365_ = lean_unsigned_to_nat(1u);
v___x_4366_ = lean_unsigned_to_nat(0u);
v_bs_x27_4367_ = lean_array_uset(v_bs_4358_, v_i_4357_, v___x_4366_);
v_ts_4368_ = l_Lean_Syntax_getArg(v_v_4361_, v___x_4365_);
lean_dec(v_v_4361_);
v___x_4369_ = ((size_t)1ULL);
v___x_4370_ = lean_usize_add(v_i_4357_, v___x_4369_);
v___x_4371_ = lean_array_uset(v_bs_x27_4367_, v_i_4357_, v_ts_4368_);
v_i_4357_ = v___x_4370_;
v_bs_4358_ = v___x_4371_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0___boxed(lean_object* v_sz_4373_, lean_object* v_i_4374_, lean_object* v_bs_4375_){
_start:
{
size_t v_sz_boxed_4376_; size_t v_i_boxed_4377_; lean_object* v_res_4378_; 
v_sz_boxed_4376_ = lean_unbox_usize(v_sz_4373_);
lean_dec(v_sz_4373_);
v_i_boxed_4377_ = lean_unbox_usize(v_i_4374_);
lean_dec(v_i_4374_);
v_res_4378_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_boxed_4376_, v_i_boxed_4377_, v_bs_4375_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(lean_object* v___x_4385_, size_t v_sz_4386_, size_t v_i_4387_, lean_object* v_bs_4388_){
_start:
{
uint8_t v___x_4389_; 
v___x_4389_ = lean_usize_dec_lt(v_i_4387_, v_sz_4386_);
if (v___x_4389_ == 0)
{
lean_dec(v___x_4385_);
return v_bs_4388_;
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v_v_4393_; lean_object* v___x_4394_; lean_object* v_bs_x27_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; lean_object* v___x_4417_; 
v___x_4390_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4391_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4392_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v_v_4393_ = lean_array_uget(v_bs_4388_, v_i_4387_);
v___x_4394_ = lean_unsigned_to_nat(0u);
v_bs_x27_4395_ = lean_array_uset(v_bs_4388_, v_i_4387_, v___x_4394_);
v___x_4396_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__38));
v___x_4397_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
lean_inc_n(v___x_4385_, 11);
v___x_4398_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4385_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__15));
v___x_4400_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
v___x_4401_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4385_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4403_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4385_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = l_Lean_Syntax_node3(v___x_4385_, v___x_4399_, v___x_4401_, v_v_4393_, v___x_4403_);
v___x_4405_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__tacticFunext________1___closed__8));
v___x_4406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4385_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__0));
v___x_4408_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___closed__1));
v___x_4409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4385_);
lean_ctor_set(v___x_4409_, 1, v___x_4407_);
v___x_4410_ = l_Lean_Syntax_node1(v___x_4385_, v___x_4408_, v___x_4409_);
v___x_4411_ = l_Lean_Syntax_node3(v___x_4385_, v___x_4391_, v___x_4404_, v___x_4406_, v___x_4410_);
v___x_4412_ = l_Lean_Syntax_node1(v___x_4385_, v___x_4390_, v___x_4411_);
v___x_4413_ = l_Lean_Syntax_node1(v___x_4385_, v___x_4392_, v___x_4412_);
v___x_4414_ = l_Lean_Syntax_node2(v___x_4385_, v___x_4396_, v___x_4398_, v___x_4413_);
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4387_, v___x_4415_);
v___x_4417_ = lean_array_uset(v_bs_x27_4395_, v_i_4387_, v___x_4414_);
v_i_4387_ = v___x_4416_;
v_bs_4388_ = v___x_4417_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1___boxed(lean_object* v___x_4419_, lean_object* v_sz_4420_, lean_object* v_i_4421_, lean_object* v_bs_4422_){
_start:
{
size_t v_sz_boxed_4423_; size_t v_i_boxed_4424_; lean_object* v_res_4425_; 
v_sz_boxed_4423_ = lean_unbox_usize(v_sz_4420_);
lean_dec(v_sz_4420_);
v_i_boxed_4424_ = lean_unbox_usize(v_i_4421_);
lean_dec(v_i_4421_);
v_res_4425_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4419_, v_sz_boxed_4423_, v_i_boxed_4424_, v_bs_4422_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(lean_object* v_x_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_){
_start:
{
lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4441_ = ((lean_object*)(l_Lean_solveTactic___closed__1));
lean_inc(v_x_4438_);
v___x_4442_ = l_Lean_Syntax_isOfKind(v_x_4438_, v___x_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_dec(v_x_4438_);
v___x_4443_ = lean_box(1);
v___x_4444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4443_);
lean_ctor_set(v___x_4444_, 1, v_a_4440_);
return v___x_4444_;
}
else
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; size_t v_sz_4448_; size_t v___x_4449_; lean_object* v___x_4450_; 
v___x_4445_ = lean_unsigned_to_nat(1u);
v___x_4446_ = l_Lean_Syntax_getArg(v_x_4438_, v___x_4445_);
lean_dec(v_x_4438_);
v___x_4447_ = l_Lean_Syntax_getArgs(v___x_4446_);
lean_dec(v___x_4446_);
v_sz_4448_ = lean_array_size(v___x_4447_);
v___x_4449_ = ((size_t)0ULL);
v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__0(v_sz_4448_, v___x_4449_, v___x_4447_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4451_ = lean_box(1);
v___x_4452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
lean_ctor_set(v___x_4452_, 1, v_a_4440_);
return v___x_4452_;
}
else
{
lean_object* v_val_4453_; lean_object* v_ref_4454_; uint8_t v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; size_t v_sz_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; 
v_val_4453_ = lean_ctor_get(v___x_4450_, 0);
lean_inc(v_val_4453_);
lean_dec_ref_known(v___x_4450_, 1);
v_ref_4454_ = lean_ctor_get(v_a_4439_, 5);
v___x_4455_ = 0;
v___x_4456_ = l_Lean_SourceInfo_fromRef(v_ref_4454_, v___x_4455_);
v___x_4457_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__0));
v___x_4458_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__1));
lean_inc_n(v___x_4456_, 8);
v___x_4459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4456_);
lean_ctor_set(v___x_4459_, 1, v___x_4457_);
v___x_4460_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__6));
v___x_4461_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__convCalc____1___closed__8));
v___x_4462_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4463_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__2));
v___x_4464_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___closed__3));
v___x_4465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4456_);
lean_ctor_set(v___x_4465_, 1, v___x_4463_);
v___x_4466_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v_sz_4467_ = lean_array_size(v_val_4453_);
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1_spec__1(v___x_4456_, v_sz_4467_, v___x_4449_, v_val_4453_);
v___x_4469_ = l_Array_append___redArg(v___x_4466_, v___x_4468_);
lean_dec_ref(v___x_4468_);
v___x_4470_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4456_);
lean_ctor_set(v___x_4470_, 1, v___x_4462_);
lean_ctor_set(v___x_4470_, 2, v___x_4469_);
v___x_4471_ = l_Lean_Syntax_node2(v___x_4456_, v___x_4464_, v___x_4465_, v___x_4470_);
v___x_4472_ = l_Lean_Syntax_node1(v___x_4456_, v___x_4462_, v___x_4471_);
v___x_4473_ = l_Lean_Syntax_node1(v___x_4456_, v___x_4461_, v___x_4472_);
v___x_4474_ = l_Lean_Syntax_node1(v___x_4456_, v___x_4460_, v___x_4473_);
v___x_4475_ = l_Lean_Syntax_node2(v___x_4456_, v___x_4458_, v___x_4459_, v___x_4474_);
v___x_4476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4476_, 0, v___x_4475_);
lean_ctor_set(v___x_4476_, 1, v_a_4440_);
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1___boxed(lean_object* v_x_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__solveTactic__1(v_x_4477_, v_a_4478_, v_a_4479_);
lean_dec_ref(v_a_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(lean_object* v___x_4509_, size_t v_sz_4510_, size_t v_i_4511_, lean_object* v_bs_4512_){
_start:
{
uint8_t v___x_4513_; 
v___x_4513_ = lean_usize_dec_lt(v_i_4511_, v_sz_4510_);
if (v___x_4513_ == 0)
{
lean_dec(v___x_4509_);
return v_bs_4512_;
}
else
{
lean_object* v___x_4514_; lean_object* v_v_4515_; lean_object* v___x_4516_; lean_object* v_bs_x27_4517_; lean_object* v___x_4518_; size_t v___x_4519_; size_t v___x_4520_; lean_object* v___x_4521_; 
v___x_4514_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v_v_4515_ = lean_array_uget(v_bs_4512_, v_i_4511_);
v___x_4516_ = lean_unsigned_to_nat(0u);
v_bs_x27_4517_ = lean_array_uset(v_bs_4512_, v_i_4511_, v___x_4516_);
lean_inc(v___x_4509_);
v___x_4518_ = l_Lean_Syntax_node1(v___x_4509_, v___x_4514_, v_v_4515_);
v___x_4519_ = ((size_t)1ULL);
v___x_4520_ = lean_usize_add(v_i_4511_, v___x_4519_);
v___x_4521_ = lean_array_uset(v_bs_x27_4517_, v_i_4511_, v___x_4518_);
v_i_4511_ = v___x_4520_;
v_bs_4512_ = v___x_4521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0___boxed(lean_object* v___x_4523_, lean_object* v_sz_4524_, lean_object* v_i_4525_, lean_object* v_bs_4526_){
_start:
{
size_t v_sz_boxed_4527_; size_t v_i_boxed_4528_; lean_object* v_res_4529_; 
v_sz_boxed_4527_ = lean_unbox_usize(v_sz_4524_);
lean_dec(v_sz_4524_);
v_i_boxed_4528_ = lean_unbox_usize(v_i_4525_);
lean_dec(v_i_4525_);
v_res_4529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4523_, v_sz_boxed_4527_, v_i_boxed_4528_, v_bs_4526_);
return v_res_4529_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11(void){
_start:
{
lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4563_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4564_ = l_Lean_mkAtom(v___x_4563_);
return v___x_4564_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__12));
v___x_4567_ = l_String_toRawSubstring_x27(v___x_4566_);
return v___x_4567_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20(void){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
v___x_4581_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__19));
v___x_4582_ = l_String_toRawSubstring_x27(v___x_4581_);
return v___x_4582_;
}
}
static lean_object* _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25(void){
_start:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4594_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__15));
v___x_4595_ = l_String_toRawSubstring_x27(v___x_4594_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(lean_object* v_x_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___x_4612_; uint8_t v___x_4613_; 
v___x_4612_ = ((lean_object*)(l_Lean_term__Matches___x7c___closed__1));
lean_inc(v_x_4609_);
v___x_4613_ = l_Lean_Syntax_isOfKind(v_x_4609_, v___x_4612_);
if (v___x_4613_ == 0)
{
lean_object* v___x_4614_; lean_object* v___x_4615_; 
lean_dec(v_x_4609_);
v___x_4614_ = lean_box(1);
v___x_4615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
lean_ctor_set(v___x_4615_, 1, v_a_4611_);
return v___x_4615_;
}
else
{
lean_object* v_quotContext_4616_; lean_object* v_currMacroScope_4617_; lean_object* v_ref_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v_p_4623_; uint8_t v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; size_t v_sz_4655_; size_t v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_quotContext_4616_ = lean_ctor_get(v_a_4610_, 1);
v_currMacroScope_4617_ = lean_ctor_get(v_a_4610_, 2);
v_ref_4618_ = lean_ctor_get(v_a_4610_, 5);
v___x_4619_ = lean_unsigned_to_nat(0u);
v___x_4620_ = l_Lean_Syntax_getArg(v_x_4609_, v___x_4619_);
v___x_4621_ = lean_unsigned_to_nat(2u);
v___x_4622_ = l_Lean_Syntax_getArg(v_x_4609_, v___x_4621_);
lean_dec(v_x_4609_);
v_p_4623_ = l_Lean_Syntax_getArgs(v___x_4622_);
lean_dec(v___x_4622_);
v___x_4624_ = 0;
v___x_4625_ = l_Lean_SourceInfo_fromRef(v_ref_4618_, v___x_4624_);
v___x_4626_ = ((lean_object*)(l_unexpandExists___closed__1));
v___x_4627_ = ((lean_object*)(l_unexpandUnit___redArg___closed__5));
v___x_4628_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__2));
lean_inc_n(v___x_4625_, 29);
v___x_4629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4625_);
lean_ctor_set(v___x_4629_, 1, v___x_4628_);
v___x_4630_ = ((lean_object*)(l_unexpandUnit___redArg___closed__7));
v___x_4631_ = lean_obj_once(&l_unexpandUnit___redArg___closed__9, &l_unexpandUnit___redArg___closed__9_once, _init_l_unexpandUnit___redArg___closed__9);
v___x_4632_ = lean_box(0);
lean_inc_n(v_currMacroScope_4617_, 4);
lean_inc_n(v_quotContext_4616_, 4);
v___x_4633_ = l_Lean_addMacroScope(v_quotContext_4616_, v___x_4632_, v_currMacroScope_4617_);
v___x_4634_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__0));
v___x_4635_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4625_);
lean_ctor_set(v___x_4635_, 1, v___x_4631_);
lean_ctor_set(v___x_4635_, 2, v___x_4633_);
lean_ctor_set(v___x_4635_, 3, v___x_4634_);
v___x_4636_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4630_, v___x_4635_);
v___x_4637_ = l_Lean_Syntax_node2(v___x_4625_, v___x_4627_, v___x_4629_, v___x_4636_);
v___x_4638_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__1));
v___x_4639_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__2));
v___x_4640_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__3));
v___x_4641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4641_, 0, v___x_4625_);
lean_ctor_set(v___x_4641_, 1, v___x_4639_);
v___x_4642_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4643_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4644_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4625_);
lean_ctor_set(v___x_4644_, 1, v___x_4642_);
lean_ctor_set(v___x_4644_, 2, v___x_4643_);
v___x_4645_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__5));
lean_inc_ref_n(v___x_4644_, 2);
v___x_4646_ = l_Lean_Syntax_node2(v___x_4625_, v___x_4645_, v___x_4644_, v___x_4620_);
v___x_4647_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4642_, v___x_4646_);
v___x_4648_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__6));
v___x_4649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4649_, 0, v___x_4625_);
lean_ctor_set(v___x_4649_, 1, v___x_4648_);
v___x_4650_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__8));
v___x_4651_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__10));
v___x_4652_ = ((lean_object*)(l_Lean_command____Unif__hint________Where___x7c___x2d_u22a2_____00__closed__41));
v___x_4653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4625_);
lean_ctor_set(v___x_4653_, 1, v___x_4652_);
v___x_4654_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_p_4623_);
lean_dec_ref(v_p_4623_);
v_sz_4655_ = lean_array_size(v___x_4654_);
v___x_4656_ = ((size_t)0ULL);
v___x_4657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1_spec__0(v___x_4625_, v_sz_4655_, v___x_4656_, v___x_4654_);
v___x_4658_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__11);
v___x_4659_ = l_Lean_mkSepArray(v___x_4657_, v___x_4658_);
lean_dec_ref(v___x_4657_);
v___x_4660_ = l_Array_append___redArg(v___x_4643_, v___x_4659_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4661_, 0, v___x_4625_);
lean_ctor_set(v___x_4661_, 1, v___x_4642_);
lean_ctor_set(v___x_4661_, 2, v___x_4660_);
v___x_4662_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__14));
v___x_4663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4625_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
v___x_4664_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__13);
v___x_4665_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__14));
v___x_4666_ = l_Lean_addMacroScope(v_quotContext_4616_, v___x_4665_, v_currMacroScope_4617_);
v___x_4667_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__18));
v___x_4668_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4625_);
lean_ctor_set(v___x_4668_, 1, v___x_4664_);
lean_ctor_set(v___x_4668_, 2, v___x_4666_);
lean_ctor_set(v___x_4668_, 3, v___x_4667_);
lean_inc_ref(v___x_4663_);
lean_inc_ref(v___x_4653_);
v___x_4669_ = l_Lean_Syntax_node4(v___x_4625_, v___x_4651_, v___x_4653_, v___x_4661_, v___x_4663_, v___x_4668_);
v___x_4670_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__11));
v___x_4671_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__12));
v___x_4672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4625_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
v___x_4673_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4670_, v___x_4672_);
v___x_4674_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4642_, v___x_4673_);
v___x_4675_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4642_, v___x_4674_);
v___x_4676_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__20);
v___x_4677_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__21));
v___x_4678_ = l_Lean_addMacroScope(v_quotContext_4616_, v___x_4677_, v_currMacroScope_4617_);
v___x_4679_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__24));
v___x_4680_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4625_);
lean_ctor_set(v___x_4680_, 1, v___x_4676_);
lean_ctor_set(v___x_4680_, 2, v___x_4678_);
lean_ctor_set(v___x_4680_, 3, v___x_4679_);
v___x_4681_ = l_Lean_Syntax_node4(v___x_4625_, v___x_4651_, v___x_4653_, v___x_4675_, v___x_4663_, v___x_4680_);
v___x_4682_ = l_Lean_Syntax_node2(v___x_4625_, v___x_4642_, v___x_4669_, v___x_4681_);
v___x_4683_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4650_, v___x_4682_);
v___x_4684_ = l_Lean_Syntax_node6(v___x_4625_, v___x_4640_, v___x_4641_, v___x_4644_, v___x_4644_, v___x_4647_, v___x_4649_, v___x_4683_);
v___x_4685_ = ((lean_object*)(l_Lean_bracketedExplicitBinders___closed__14));
v___x_4686_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4625_);
lean_ctor_set(v___x_4686_, 1, v___x_4685_);
lean_inc_ref(v___x_4686_);
lean_inc(v___x_4637_);
v___x_4687_ = l_Lean_Syntax_node3(v___x_4625_, v___x_4638_, v___x_4637_, v___x_4684_, v___x_4686_);
v___x_4688_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__17));
v___x_4689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4625_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
v___x_4690_ = lean_obj_once(&l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25, &l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25_once, _init_l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__25);
v___x_4691_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__26));
v___x_4692_ = l_Lean_addMacroScope(v_quotContext_4616_, v___x_4691_, v_currMacroScope_4617_);
v___x_4693_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___closed__30));
v___x_4694_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4625_);
lean_ctor_set(v___x_4694_, 1, v___x_4690_);
lean_ctor_set(v___x_4694_, 2, v___x_4692_);
lean_ctor_set(v___x_4694_, 3, v___x_4693_);
v___x_4695_ = l_Lean_Syntax_node1(v___x_4625_, v___x_4642_, v___x_4694_);
v___x_4696_ = l_Lean_Syntax_node5(v___x_4625_, v___x_4626_, v___x_4637_, v___x_4687_, v___x_4689_, v___x_4695_, v___x_4686_);
v___x_4697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v_a_4611_);
return v___x_4697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1___boxed(lean_object* v_x_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean___aux__Init__NotationExtra______macroRules__Lean__term__Matches___x7c__1(v_x_4698_, v_a_4699_, v_a_4700_);
lean_dec_ref(v_a_4699_);
return v_res_4701_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1(void){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__0));
v___x_4732_ = l_String_toRawSubstring_x27(v___x_4731_);
return v___x_4732_;
}
}
static lean_object* _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8(void){
_start:
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__7));
v___x_4747_ = l_String_toRawSubstring_x27(v___x_4746_);
return v___x_4747_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(lean_object* v_x_4760_, lean_object* v_a_4761_, lean_object* v_a_4762_){
_start:
{
lean_object* v___x_4763_; uint8_t v___x_4764_; 
v___x_4763_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v_x_4760_);
v___x_4764_ = l_Lean_Syntax_isOfKind(v_x_4760_, v___x_4763_);
if (v___x_4764_ == 0)
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec(v_x_4760_);
v___x_4765_ = lean_box(1);
v___x_4766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
lean_ctor_set(v___x_4766_, 1, v_a_4762_);
return v___x_4766_;
}
else
{
lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; uint8_t v___x_4770_; 
v___x_4767_ = lean_unsigned_to_nat(0u);
v___x_4768_ = lean_unsigned_to_nat(1u);
v___x_4769_ = l_Lean_Syntax_getArg(v_x_4760_, v___x_4768_);
lean_dec(v_x_4760_);
lean_inc(v___x_4769_);
v___x_4770_ = l_Lean_Syntax_matchesNull(v___x_4769_, v___x_4768_);
if (v___x_4770_ == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; uint8_t v___x_4773_; 
v___x_4771_ = lean_unsigned_to_nat(2u);
v___x_4772_ = l_Lean_Syntax_getNumArgs(v___x_4769_);
v___x_4773_ = lean_nat_dec_le(v___x_4771_, v___x_4772_);
if (v___x_4773_ == 0)
{
lean_object* v___x_4774_; lean_object* v___x_4775_; 
lean_dec(v___x_4772_);
lean_dec(v___x_4769_);
v___x_4774_ = lean_box(1);
v___x_4775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4774_);
lean_ctor_set(v___x_4775_, 1, v_a_4762_);
return v___x_4775_;
}
else
{
lean_object* v_quotContext_4776_; lean_object* v_currMacroScope_4777_; lean_object* v_ref_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; 
v_quotContext_4776_ = lean_ctor_get(v_a_4761_, 1);
v_currMacroScope_4777_ = lean_ctor_get(v_a_4761_, 2);
v_ref_4778_ = lean_ctor_get(v_a_4761_, 5);
v___x_4779_ = l_Lean_Syntax_getArg(v___x_4769_, v___x_4767_);
v___x_4780_ = l_Lean_Syntax_getArgs(v___x_4769_);
lean_dec(v___x_4769_);
v___x_4781_ = l_Array_extract___redArg(v___x_4780_, v___x_4771_, v___x_4772_);
lean_dec_ref(v___x_4780_);
v___x_4782_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4783_ = lean_box(2);
v___x_4784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4783_);
lean_ctor_set(v___x_4784_, 1, v___x_4782_);
lean_ctor_set(v___x_4784_, 2, v___x_4781_);
v___x_4785_ = l_Lean_Syntax_getArgs(v___x_4784_);
lean_dec_ref_known(v___x_4784_, 3);
v___x_4786_ = l_Lean_SourceInfo_fromRef(v_ref_4778_, v___x_4770_);
v___x_4787_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4788_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__1);
v___x_4789_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__2));
lean_inc(v_currMacroScope_4777_);
lean_inc(v_quotContext_4776_);
v___x_4790_ = l_Lean_addMacroScope(v_quotContext_4776_, v___x_4789_, v_currMacroScope_4777_);
v___x_4791_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__6));
lean_inc_n(v___x_4786_, 6);
v___x_4792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4786_);
lean_ctor_set(v___x_4792_, 1, v___x_4788_);
lean_ctor_set(v___x_4792_, 2, v___x_4790_);
lean_ctor_set(v___x_4792_, 3, v___x_4791_);
v___x_4793_ = ((lean_object*)(l_unexpandSubtype___closed__2));
v___x_4794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4786_);
lean_ctor_set(v___x_4794_, 1, v___x_4793_);
v___x_4795_ = lean_obj_once(&l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13, &l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13_once, _init_l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__13);
v___x_4796_ = l_Array_append___redArg(v___x_4795_, v___x_4785_);
lean_dec_ref(v___x_4785_);
v___x_4797_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4786_);
lean_ctor_set(v___x_4797_, 1, v___x_4782_);
lean_ctor_set(v___x_4797_, 2, v___x_4796_);
v___x_4798_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4799_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4786_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = l_Lean_Syntax_node3(v___x_4786_, v___x_4763_, v___x_4794_, v___x_4797_, v___x_4799_);
v___x_4801_ = l_Lean_Syntax_node2(v___x_4786_, v___x_4782_, v___x_4779_, v___x_4800_);
v___x_4802_ = l_Lean_Syntax_node2(v___x_4786_, v___x_4787_, v___x_4792_, v___x_4801_);
v___x_4803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4802_);
lean_ctor_set(v___x_4803_, 1, v_a_4762_);
return v___x_4803_;
}
}
else
{
lean_object* v_quotContext_4804_; lean_object* v_currMacroScope_4805_; lean_object* v_ref_4806_; lean_object* v___x_4807_; uint8_t v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v_quotContext_4804_ = lean_ctor_get(v_a_4761_, 1);
v_currMacroScope_4805_ = lean_ctor_get(v_a_4761_, 2);
v_ref_4806_ = lean_ctor_get(v_a_4761_, 5);
v___x_4807_ = l_Lean_Syntax_getArg(v___x_4769_, v___x_4767_);
lean_dec(v___x_4769_);
v___x_4808_ = 0;
v___x_4809_ = l_Lean_SourceInfo_fromRef(v_ref_4806_, v___x_4808_);
v___x_4810_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
v___x_4811_ = lean_obj_once(&l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8, &l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8_once, _init_l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__8);
v___x_4812_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__9));
lean_inc(v_currMacroScope_4805_);
lean_inc(v_quotContext_4804_);
v___x_4813_ = l_Lean_addMacroScope(v_quotContext_4804_, v___x_4812_, v_currMacroScope_4805_);
v___x_4814_ = ((lean_object*)(l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___closed__13));
lean_inc_n(v___x_4809_, 2);
v___x_4815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4809_);
lean_ctor_set(v___x_4815_, 1, v___x_4811_);
lean_ctor_set(v___x_4815_, 2, v___x_4813_);
lean_ctor_set(v___x_4815_, 3, v___x_4814_);
v___x_4816_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4817_ = l_Lean_Syntax_node1(v___x_4809_, v___x_4816_, v___x_4807_);
v___x_4818_ = l_Lean_Syntax_node2(v___x_4809_, v___x_4810_, v___x_4815_, v___x_4817_);
v___x_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
lean_ctor_set(v___x_4819_, 1, v_a_4762_);
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1___boxed(lean_object* v_x_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_){
_start:
{
lean_object* v_res_4823_; 
v_res_4823_ = l___aux__Init__NotationExtra______macroRules__term_x7b___x7d__1(v_x_4820_, v_a_4821_, v_a_4822_);
lean_dec_ref(v_a_4821_);
return v_res_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander(lean_object* v_x_4824_, lean_object* v_a_4825_, lean_object* v_a_4826_){
_start:
{
lean_object* v___x_4827_; uint8_t v___x_4828_; 
v___x_4827_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_4824_);
v___x_4828_ = l_Lean_Syntax_isOfKind(v_x_4824_, v___x_4827_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
lean_dec(v_x_4824_);
v___x_4829_ = lean_box(0);
v___x_4830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4829_);
lean_ctor_set(v___x_4830_, 1, v_a_4826_);
return v___x_4830_;
}
else
{
lean_object* v___x_4831_; lean_object* v___x_4832_; uint8_t v___x_4833_; 
v___x_4831_ = lean_unsigned_to_nat(1u);
v___x_4832_ = l_Lean_Syntax_getArg(v_x_4824_, v___x_4831_);
lean_dec(v_x_4824_);
lean_inc(v___x_4832_);
v___x_4833_ = l_Lean_Syntax_matchesNull(v___x_4832_, v___x_4831_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_dec(v___x_4832_);
v___x_4834_ = lean_box(0);
v___x_4835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4835_, 0, v___x_4834_);
lean_ctor_set(v___x_4835_, 1, v_a_4826_);
return v___x_4835_;
}
else
{
lean_object* v___x_4836_; lean_object* v___x_4837_; uint8_t v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4836_ = lean_unsigned_to_nat(0u);
v___x_4837_ = l_Lean_Syntax_getArg(v___x_4832_, v___x_4836_);
lean_dec(v___x_4832_);
v___x_4838_ = 0;
v___x_4839_ = l_Lean_SourceInfo_fromRef(v_a_4825_, v___x_4838_);
v___x_4840_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
v___x_4841_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_4839_, 3);
v___x_4842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4839_);
lean_ctor_set(v___x_4842_, 1, v___x_4841_);
v___x_4843_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4844_ = l_Lean_Syntax_node1(v___x_4839_, v___x_4843_, v___x_4837_);
v___x_4845_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4839_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
v___x_4847_ = l_Lean_Syntax_node3(v___x_4839_, v___x_4840_, v___x_4842_, v___x_4844_, v___x_4846_);
v___x_4848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v_a_4826_);
return v___x_4848_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_singletonUnexpander___boxed(lean_object* v_x_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
lean_object* v_res_4852_; 
v_res_4852_ = l_Lean_singletonUnexpander(v_x_4849_, v_a_4850_, v_a_4851_);
lean_dec(v_a_4850_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander(lean_object* v_x_4853_, lean_object* v_a_4854_, lean_object* v_a_4855_){
_start:
{
lean_object* v___x_4856_; uint8_t v___x_4857_; 
v___x_4856_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__3));
lean_inc(v_x_4853_);
v___x_4857_ = l_Lean_Syntax_isOfKind(v_x_4853_, v___x_4856_);
if (v___x_4857_ == 0)
{
lean_object* v___x_4858_; lean_object* v___x_4859_; 
lean_dec(v_x_4853_);
v___x_4858_ = lean_box(0);
v___x_4859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4859_, 0, v___x_4858_);
lean_ctor_set(v___x_4859_, 1, v_a_4855_);
return v___x_4859_;
}
else
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; uint8_t v___x_4863_; 
v___x_4860_ = lean_unsigned_to_nat(1u);
v___x_4861_ = l_Lean_Syntax_getArg(v_x_4853_, v___x_4860_);
lean_dec(v_x_4853_);
v___x_4862_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4861_);
v___x_4863_ = l_Lean_Syntax_matchesNull(v___x_4861_, v___x_4862_);
if (v___x_4863_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
lean_dec(v___x_4861_);
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4864_);
lean_ctor_set(v___x_4865_, 1, v_a_4855_);
return v___x_4865_;
}
else
{
lean_object* v___x_4866_; lean_object* v___x_4867_; uint8_t v___x_4868_; 
v___x_4866_ = l_Lean_Syntax_getArg(v___x_4861_, v___x_4860_);
v___x_4867_ = ((lean_object*)(l_term_x7b___x7d___closed__1));
lean_inc(v___x_4866_);
v___x_4868_ = l_Lean_Syntax_isOfKind(v___x_4866_, v___x_4867_);
if (v___x_4868_ == 0)
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
lean_dec(v___x_4866_);
lean_dec(v___x_4861_);
v___x_4869_ = lean_box(0);
v___x_4870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
lean_ctor_set(v___x_4870_, 1, v_a_4855_);
return v___x_4870_;
}
else
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4871_ = lean_unsigned_to_nat(0u);
v___x_4872_ = l_Lean_Syntax_getArg(v___x_4861_, v___x_4871_);
lean_dec(v___x_4861_);
v___x_4873_ = l_Lean_Syntax_getArg(v___x_4866_, v___x_4860_);
lean_dec(v___x_4866_);
v___x_4874_ = ((lean_object*)(l_Lean___aux__Init__NotationExtra______macroRules__Lean__command____Unif__hint________Where___x7c___x2d_u22a2______1___closed__17));
v___x_4875_ = l_Lean_Syntax_getArgs(v___x_4873_);
lean_dec(v___x_4873_);
v___x_4876_ = 0;
v___x_4877_ = l_Lean_SourceInfo_fromRef(v_a_4854_, v___x_4876_);
v___x_4878_ = ((lean_object*)(l_unexpandSubtype___closed__2));
lean_inc_n(v___x_4877_, 4);
v___x_4879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = ((lean_object*)(l___private_Init_NotationExtra_0__Lean_expandExplicitBindersAux_loop___redArg___closed__5));
v___x_4881_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4877_);
lean_ctor_set(v___x_4881_, 1, v___x_4874_);
v___x_4882_ = l_Array_mkArray2___redArg(v___x_4872_, v___x_4881_);
v___x_4883_ = l_Array_append___redArg(v___x_4882_, v___x_4875_);
lean_dec_ref(v___x_4875_);
v___x_4884_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4877_);
lean_ctor_set(v___x_4884_, 1, v___x_4880_);
lean_ctor_set(v___x_4884_, 2, v___x_4883_);
v___x_4885_ = ((lean_object*)(l_unexpandSubtype___closed__4));
v___x_4886_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4877_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = l_Lean_Syntax_node3(v___x_4877_, v___x_4867_, v___x_4879_, v___x_4884_, v___x_4886_);
v___x_4888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
lean_ctor_set(v___x_4888_, 1, v_a_4855_);
return v___x_4888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_insertUnexpander___boxed(lean_object* v_x_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v_res_4892_; 
v_res_4892_ = l_Lean_insertUnexpander(v_x_4889_, v_a_4890_, v_a_4891_);
lean_dec(v_a_4890_);
return v_res_4892_;
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
