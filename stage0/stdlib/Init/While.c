// Lean compiler output
// Module: Init.While
// Imports: public import Init.Core
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemRepeat___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_doElemRepeat___00__closed__0 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__0_value;
static const lean_string_object l_Lean_doElemRepeat___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doElemRepeat_"};
static const lean_object* l_Lean_doElemRepeat___00__closed__1 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__1_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__2_value_aux_0),((lean_object*)&l_Lean_doElemRepeat___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(239, 116, 64, 138, 184, 166, 80, 202)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__2 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__2_value;
static const lean_string_object l_Lean_doElemRepeat___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_doElemRepeat___00__closed__3 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__3_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__4 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__4_value;
static const lean_string_object l_Lean_doElemRepeat___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "repeat "};
static const lean_object* l_Lean_doElemRepeat___00__closed__5 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__5_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__5_value)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__6 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__6_value;
static const lean_string_object l_Lean_doElemRepeat___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doSeq"};
static const lean_object* l_Lean_doElemRepeat___00__closed__7 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__7_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__7_value),LEAN_SCALAR_PTR_LITERAL(87, 108, 208, 147, 238, 58, 86, 179)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__8 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__8_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__8_value)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__9 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__9_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemRepeat___00__closed__6_value),((lean_object*)&l_Lean_doElemRepeat___00__closed__9_value)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__10 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__10_value;
static const lean_ctor_object l_Lean_doElemRepeat___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__2_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__10_value)}};
static const lean_object* l_Lean_doElemRepeat___00__closed__11 = (const lean_object*)&l_Lean_doElemRepeat___00__closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_doElemRepeat__ = (const lean_object*)&l_Lean_doElemRepeat___00__closed__11_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__2_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "for"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__4_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__5 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__7 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__7_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8_value;
static lean_once_cell_t l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__10 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__10_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__12 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__12_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__13 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__13_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Loop.mk"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__14 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__14_value;
static lean_once_cell_t l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Loop"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__16 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__16_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__17 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__17_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(77, 134, 225, 236, 222, 42, 27, 28)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(121, 43, 2, 225, 80, 67, 164, 196)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(244, 180, 170, 243, 159, 48, 205, 98)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(92, 204, 229, 77, 211, 121, 59, 130)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__20 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__20_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__19_value)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__21 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__21_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__22 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__22_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__20_value),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__22_value)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__23 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__23_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "do"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__24 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__24_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "doElemWhile_:_Do_"};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__0 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__0_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__1_value_aux_0),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 252, 200, 77, 9, 164, 27, 211)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__1 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__1_value;
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "while "};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__2 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__2_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__2_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__3 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__3_value;
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__4 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__4_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__5 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__5_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__5_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__6 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__6_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__3_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__6_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__7 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__7_value;
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__8 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__8_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__8_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__9 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__9_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__7_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__9_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__10 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__10_value;
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termBeforeDo"};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__11 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__11_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__11_value),LEAN_SCALAR_PTR_LITERAL(169, 45, 190, 25, 137, 37, 211, 187)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__12 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__12_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__12_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__13 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__13_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__10_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__13_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__14 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__14_value;
static const lean_string_object l_Lean_doElemWhile___x3a__Do___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " do "};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__15 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__15_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__15_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__16 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__16_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__14_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__16_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__17 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__17_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__17_value),((lean_object*)&l_Lean_doElemRepeat___00__closed__9_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__18 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__18_value;
static const lean_ctor_object l_Lean_doElemWhile___x3a__Do___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__18_value)}};
static const lean_object* l_Lean_doElemWhile___x3a__Do___00__closed__19 = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__19_value;
LEAN_EXPORT const lean_object* l_Lean_doElemWhile___x3a__Do__ = (const lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__19_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "repeat"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doSeqIndent"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__1_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 115, 138, 230, 225, 195, 43, 46)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doSeqItem"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__3 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__3_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(10, 94, 50, 120, 46, 251, 13, 13)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__5 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__5_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIfProp"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__8 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__8_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(55, 147, 210, 58, 86, 191, 41, 151)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__10 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__10_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__12 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__12_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__13 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__13_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "break"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemWhile__Do___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doElemWhile_Do_"};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__0 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__0_value;
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemWhile__Do___00__closed__1_value_aux_0),((lean_object*)&l_Lean_doElemWhile__Do___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 139, 202, 220, 193, 43, 141, 225)}};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__1 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__1_value;
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__3_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__13_value)}};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__2 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__2_value;
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile__Do___00__closed__2_value),((lean_object*)&l_Lean_doElemWhile___x3a__Do___00__closed__16_value)}};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__3 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__3_value;
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemWhile__Do___00__closed__3_value),((lean_object*)&l_Lean_doElemRepeat___00__closed__9_value)}};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__4 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__4_value;
static const lean_ctor_object l_Lean_doElemWhile__Do___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemWhile__Do___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemWhile__Do___00__closed__4_value)}};
static const lean_object* l_Lean_doElemWhile__Do___00__closed__5 = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_doElemWhile__Do__ = (const lean_object*)&l_Lean_doElemWhile__Do___00__closed__5_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile__Do____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile__Do____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_doElemRepeat____Until___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "doElemRepeat__Until_"};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__0 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__0_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__1_value_aux_0),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 179, 176, 232, 137, 153, 228, 70)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__1 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__1_value;
static const lean_string_object l_Lean_doElemRepeat____Until___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ppDedent"};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__2 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__2_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(242, 37, 230, 124, 106, 100, 159, 37)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__3 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__3_value;
static const lean_string_object l_Lean_doElemRepeat____Until___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__4 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__4_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__5 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__5_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__5_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__6 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__6_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__3_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__6_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__7 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__7_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemRepeat___00__closed__10_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__7_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__8 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__8_value;
static const lean_string_object l_Lean_doElemRepeat____Until___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "until "};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__9 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__9_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__9_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__10 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__10_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__8_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__10_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__11 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__11_value;
static const lean_string_object l_Lean_doElemRepeat____Until___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__12 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__12_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__12_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__13 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__13_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__14 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__14_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat___00__closed__4_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__11_value),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__14_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__15 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__15_value;
static const lean_ctor_object l_Lean_doElemRepeat____Until___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat____Until___00__closed__15_value)}};
static const lean_object* l_Lean_doElemRepeat____Until___00__closed__16 = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__16_value;
LEAN_EXPORT const lean_object* l_Lean_doElemRepeat____Until__ = (const lean_object*)&l_Lean_doElemRepeat____Until___00__closed__16_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__0 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__0_value;
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_doElemRepeat___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_0),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_1),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value_aux_2),((lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1_value;
static const lean_string_object l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__2 = (const lean_object*)&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_toCtorIdx(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(lean_object* v_inst_3_, lean_object* v_f_4_, lean_object* v_b_5_){
_start:
{
lean_object* v_toApplicative_6_; lean_object* v_toBind_7_; lean_object* v_toPure_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___f_11_; lean_object* v___x_12_; 
v_toApplicative_6_ = lean_ctor_get(v_inst_3_, 0);
v_toBind_7_ = lean_ctor_get(v_inst_3_, 1);
lean_inc(v_toBind_7_);
v_toPure_8_ = lean_ctor_get(v_toApplicative_6_, 1);
lean_inc(v_toPure_8_);
v___x_9_ = lean_box(0);
lean_inc(v_f_4_);
v___x_10_ = lean_apply_2(v_f_4_, v___x_9_, v_b_5_);
v___f_11_ = lean_alloc_closure((void*)(l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_11_, 0, v_toPure_8_);
lean_closure_set(v___f_11_, 1, v_inst_3_);
lean_closure_set(v___f_11_, 2, v_f_4_);
v___x_12_ = lean_apply_4(v_toBind_7_, lean_box(0), lean_box(0), v___x_10_, v___f_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___redArg___lam__0(lean_object* v_toPure_13_, lean_object* v_inst_14_, lean_object* v_f_15_, lean_object* v_____do__lift_16_){
_start:
{
if (lean_obj_tag(v_____do__lift_16_) == 0)
{
lean_object* v_a_17_; lean_object* v___x_18_; 
lean_dec(v_f_15_);
lean_dec_ref(v_inst_14_);
v_a_17_ = lean_ctor_get(v_____do__lift_16_, 0);
lean_inc(v_a_17_);
lean_dec_ref(v_____do__lift_16_);
v___x_18_ = lean_apply_2(v_toPure_13_, lean_box(0), v_a_17_);
return v___x_18_;
}
else
{
lean_object* v_a_19_; lean_object* v___x_20_; 
lean_dec(v_toPure_13_);
v_a_19_ = lean_ctor_get(v_____do__lift_16_, 0);
lean_inc(v_a_19_);
lean_dec_ref(v_____do__lift_16_);
v___x_20_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_14_, v_f_15_, v_a_19_);
return v___x_20_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop(lean_object* v_00_u03b2_21_, lean_object* v_m_22_, lean_object* v_inst_23_, lean_object* v_f_24_, lean_object* v_b_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_23_, v_f_24_, v_b_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn___redArg(lean_object* v_inst_27_, lean_object* v_init_28_, lean_object* v_f_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_27_, v_f_29_, v_init_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn(lean_object* v_00_u03b2_31_, lean_object* v_m_32_, lean_object* v_inst_33_, lean_object* v_x_34_, lean_object* v_init_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_33_, v_f_36_, v_init_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg___lam__0(lean_object* v_inst_38_, lean_object* v_00_u03b2_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l___private_Init_While_0__Lean_Loop_forIn_loop___redArg(v_inst_38_, v___y_42_, v___y_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad___redArg(lean_object* v_inst_44_){
_start:
{
lean_object* v___f_45_; 
v___f_45_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_45_, 0, v_inst_44_);
return v___f_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_instForInLoopUnitOfMonad(lean_object* v_m_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___f_48_; 
v___f_48_ = lean_alloc_closure((void*)(l_Lean_instForInLoopUnitOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_48_, 0, v_inst_47_);
return v___f_48_;
}
}
static lean_object* _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Array_mkArray0(lean_box(0));
return v___x_92_;
}
}
static lean_object* _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__14));
v___x_103_ = l_String_toRawSubstring_x27(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_doElemRepeat___00__closed__2));
lean_inc(v_x_125_);
v___x_129_ = l_Lean_Syntax_isOfKind(v_x_125_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_x_125_);
v___x_130_ = lean_box(1);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_127_);
return v___x_131_;
}
else
{
lean_object* v_quotContext_132_; lean_object* v_currMacroScope_133_; lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v_quotContext_132_ = lean_ctor_get(v_a_126_, 1);
v_currMacroScope_133_ = lean_ctor_get(v_a_126_, 2);
v_ref_134_ = lean_ctor_get(v_a_126_, 5);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_125_, v___x_135_);
lean_dec(v_x_125_);
v___x_137_ = 0;
v___x_138_ = l_Lean_SourceInfo_fromRef(v_ref_134_, v___x_137_);
v___x_139_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__3));
v___x_140_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__4));
lean_inc_n(v___x_138_, 9);
v___x_141_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6));
v___x_143_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__8));
v___x_144_ = lean_obj_once(&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9, &l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9_once, _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_138_);
lean_ctor_set(v___x_145_, 1, v___x_142_);
lean_ctor_set(v___x_145_, 2, v___x_144_);
v___x_146_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__11));
v___x_147_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__12));
v___x_148_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_138_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = l_Lean_Syntax_node1(v___x_138_, v___x_146_, v___x_148_);
v___x_150_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__13));
v___x_151_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_138_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_obj_once(&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15, &l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15_once, _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__15);
v___x_153_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__18));
lean_inc(v_currMacroScope_133_);
lean_inc(v_quotContext_132_);
v___x_154_ = l_Lean_addMacroScope(v_quotContext_132_, v___x_153_, v_currMacroScope_133_);
v___x_155_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__23));
v___x_156_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_156_, 0, v___x_138_);
lean_ctor_set(v___x_156_, 1, v___x_152_);
lean_ctor_set(v___x_156_, 2, v___x_154_);
lean_ctor_set(v___x_156_, 3, v___x_155_);
v___x_157_ = l_Lean_Syntax_node4(v___x_138_, v___x_143_, v___x_145_, v___x_149_, v___x_151_, v___x_156_);
v___x_158_ = l_Lean_Syntax_node1(v___x_138_, v___x_142_, v___x_157_);
v___x_159_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__24));
v___x_160_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_138_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = l_Lean_Syntax_node4(v___x_138_, v___x_139_, v___x_141_, v___x_158_, v___x_160_, v___x_136_);
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_127_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___boxed(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1(v_x_163_, v_a_164_, v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1(lean_object* v_x_251_, lean_object* v_a_252_, lean_object* v_a_253_){
_start:
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = ((lean_object*)(l_Lean_doElemWhile___x3a__Do___00__closed__1));
lean_inc(v_x_251_);
v___x_255_ = l_Lean_Syntax_isOfKind(v_x_251_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_x_251_);
v___x_256_ = lean_box(1);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v_a_253_);
return v___x_257_;
}
else
{
lean_object* v_ref_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_ref_258_ = lean_ctor_get(v_a_252_, 5);
v___x_259_ = lean_unsigned_to_nat(1u);
v___x_260_ = l_Lean_Syntax_getArg(v_x_251_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = l_Lean_Syntax_getArg(v_x_251_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(5u);
v___x_264_ = l_Lean_Syntax_getArg(v_x_251_, v___x_263_);
lean_dec(v_x_251_);
v___x_265_ = 0;
v___x_266_ = l_Lean_SourceInfo_fromRef(v_ref_258_, v___x_265_);
v___x_267_ = ((lean_object*)(l_Lean_doElemRepeat___00__closed__2));
v___x_268_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0));
lean_inc_n(v___x_266_, 18);
v___x_269_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_266_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2));
v___x_271_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6));
v___x_272_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4));
v___x_273_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6));
v___x_274_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7));
v___x_275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_266_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9));
v___x_277_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__10));
v___x_278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_266_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_Syntax_node2(v___x_266_, v___x_271_, v___x_260_, v___x_278_);
v___x_280_ = l_Lean_Syntax_node2(v___x_266_, v___x_276_, v___x_279_, v___x_262_);
v___x_281_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11));
v___x_282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_266_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = lean_obj_once(&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9, &l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9_once, _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9);
v___x_284_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_284_, 0, v___x_266_);
lean_ctor_set(v___x_284_, 1, v___x_271_);
lean_ctor_set(v___x_284_, 2, v___x_283_);
v___x_285_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__12));
v___x_286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_266_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14));
v___x_288_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15));
v___x_289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_266_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = l_Lean_Syntax_node1(v___x_266_, v___x_287_, v___x_289_);
lean_inc_ref_n(v___x_284_, 2);
v___x_291_ = l_Lean_Syntax_node2(v___x_266_, v___x_272_, v___x_290_, v___x_284_);
v___x_292_ = l_Lean_Syntax_node1(v___x_266_, v___x_271_, v___x_291_);
v___x_293_ = l_Lean_Syntax_node1(v___x_266_, v___x_270_, v___x_292_);
v___x_294_ = l_Lean_Syntax_node2(v___x_266_, v___x_271_, v___x_286_, v___x_293_);
v___x_295_ = l_Lean_Syntax_node6(v___x_266_, v___x_273_, v___x_275_, v___x_280_, v___x_282_, v___x_264_, v___x_284_, v___x_294_);
v___x_296_ = l_Lean_Syntax_node2(v___x_266_, v___x_272_, v___x_295_, v___x_284_);
v___x_297_ = l_Lean_Syntax_node1(v___x_266_, v___x_271_, v___x_296_);
v___x_298_ = l_Lean_Syntax_node1(v___x_266_, v___x_270_, v___x_297_);
v___x_299_ = l_Lean_Syntax_node2(v___x_266_, v___x_267_, v___x_269_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_a_253_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___boxed(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1(v_x_301_, v_a_302_, v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile__Do____1(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_doElemWhile__Do___00__closed__1));
lean_inc(v_x_326_);
v___x_330_ = l_Lean_Syntax_isOfKind(v_x_326_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_x_326_);
v___x_331_ = lean_box(1);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_a_328_);
return v___x_332_;
}
else
{
lean_object* v_ref_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_ref_333_ = lean_ctor_get(v_a_327_, 5);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = l_Lean_Syntax_getArg(v_x_326_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(3u);
v___x_337_ = l_Lean_Syntax_getArg(v_x_326_, v___x_336_);
lean_dec(v_x_326_);
v___x_338_ = 0;
v___x_339_ = l_Lean_SourceInfo_fromRef(v_ref_333_, v___x_338_);
v___x_340_ = ((lean_object*)(l_Lean_doElemRepeat___00__closed__2));
v___x_341_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0));
lean_inc_n(v___x_339_, 16);
v___x_342_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_339_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2));
v___x_344_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6));
v___x_345_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4));
v___x_346_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6));
v___x_347_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7));
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_339_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9));
v___x_350_ = lean_obj_once(&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9, &l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9_once, _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9);
v___x_351_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_351_, 0, v___x_339_);
lean_ctor_set(v___x_351_, 1, v___x_344_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_inc_ref_n(v___x_351_, 3);
v___x_352_ = l_Lean_Syntax_node2(v___x_339_, v___x_349_, v___x_351_, v___x_335_);
v___x_353_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11));
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_339_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__12));
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_339_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14));
v___x_358_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15));
v___x_359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_339_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = l_Lean_Syntax_node1(v___x_339_, v___x_357_, v___x_359_);
v___x_361_ = l_Lean_Syntax_node2(v___x_339_, v___x_345_, v___x_360_, v___x_351_);
v___x_362_ = l_Lean_Syntax_node1(v___x_339_, v___x_344_, v___x_361_);
v___x_363_ = l_Lean_Syntax_node1(v___x_339_, v___x_343_, v___x_362_);
v___x_364_ = l_Lean_Syntax_node2(v___x_339_, v___x_344_, v___x_356_, v___x_363_);
v___x_365_ = l_Lean_Syntax_node6(v___x_339_, v___x_346_, v___x_348_, v___x_352_, v___x_354_, v___x_337_, v___x_351_, v___x_364_);
v___x_366_ = l_Lean_Syntax_node2(v___x_339_, v___x_345_, v___x_365_, v___x_351_);
v___x_367_ = l_Lean_Syntax_node1(v___x_339_, v___x_344_, v___x_366_);
v___x_368_ = l_Lean_Syntax_node1(v___x_339_, v___x_343_, v___x_367_);
v___x_369_ = l_Lean_Syntax_node2(v___x_339_, v___x_340_, v___x_342_, v___x_368_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v_a_328_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemWhile__Do____1___boxed(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean___aux__Init__While______macroRules__Lean__doElemWhile__Do____1(v_x_371_, v_a_372_, v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1(lean_object* v_x_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_doElemRepeat____Until___00__closed__1));
lean_inc(v_x_423_);
v___x_427_ = l_Lean_Syntax_isOfKind(v_x_423_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec(v_x_423_);
v___x_428_ = lean_box(1);
v___x_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_a_425_);
return v___x_429_;
}
else
{
lean_object* v_ref_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_ref_430_ = lean_ctor_get(v_a_424_, 5);
v___x_431_ = lean_unsigned_to_nat(1u);
v___x_432_ = l_Lean_Syntax_getArg(v_x_423_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(3u);
v___x_434_ = l_Lean_Syntax_getArg(v_x_423_, v___x_433_);
lean_dec(v_x_423_);
v___x_435_ = 0;
v___x_436_ = l_Lean_SourceInfo_fromRef(v_ref_430_, v___x_435_);
v___x_437_ = ((lean_object*)(l_Lean_doElemRepeat___00__closed__2));
v___x_438_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__0));
lean_inc_n(v___x_436_, 19);
v___x_439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_436_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__2));
v___x_441_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__6));
v___x_442_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__4));
v___x_443_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__1));
v___x_444_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__24));
v___x_445_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_436_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
v___x_446_ = l_Lean_Syntax_node2(v___x_436_, v___x_443_, v___x_445_, v___x_432_);
v___x_447_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___closed__2));
v___x_448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_436_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_Syntax_node1(v___x_436_, v___x_441_, v___x_448_);
v___x_450_ = l_Lean_Syntax_node2(v___x_436_, v___x_442_, v___x_446_, v___x_449_);
v___x_451_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__6));
v___x_452_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__7));
v___x_453_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_436_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__9));
v___x_455_ = lean_obj_once(&l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9, &l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9_once, _init_l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____1___closed__9);
v___x_456_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_456_, 0, v___x_436_);
lean_ctor_set(v___x_456_, 1, v___x_441_);
lean_ctor_set(v___x_456_, 2, v___x_455_);
lean_inc_ref_n(v___x_456_, 4);
v___x_457_ = l_Lean_Syntax_node2(v___x_436_, v___x_454_, v___x_456_, v___x_434_);
v___x_458_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__11));
v___x_459_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_436_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__14));
v___x_461_ = ((lean_object*)(l_Lean___aux__Init__While______macroRules__Lean__doElemWhile___x3a__Do____1___closed__15));
v___x_462_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_436_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_Syntax_node1(v___x_436_, v___x_460_, v___x_462_);
v___x_464_ = l_Lean_Syntax_node2(v___x_436_, v___x_442_, v___x_463_, v___x_456_);
v___x_465_ = l_Lean_Syntax_node1(v___x_436_, v___x_441_, v___x_464_);
v___x_466_ = l_Lean_Syntax_node1(v___x_436_, v___x_440_, v___x_465_);
v___x_467_ = l_Lean_Syntax_node6(v___x_436_, v___x_451_, v___x_453_, v___x_457_, v___x_459_, v___x_466_, v___x_456_, v___x_456_);
v___x_468_ = l_Lean_Syntax_node2(v___x_436_, v___x_442_, v___x_467_, v___x_456_);
v___x_469_ = l_Lean_Syntax_node2(v___x_436_, v___x_441_, v___x_450_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node1(v___x_436_, v___x_440_, v___x_469_);
v___x_471_ = l_Lean_Syntax_node2(v___x_436_, v___x_437_, v___x_439_, v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_a_425_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1___boxed(lean_object* v_x_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean___aux__Init__While______macroRules__Lean__doElemRepeat____Until____1(v_x_473_, v_a_474_, v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_476_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_While(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_While(builtin);
}
#ifdef __cplusplus
}
#endif
