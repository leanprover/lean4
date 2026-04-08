// Lean compiler output
// Module: Init.Data.SInt.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.SInt.Basic import all Init.Data.SInt.Basic import all Init.Data.BitVec.Basic import all Init.Data.UInt.Basic public import Init.Data.BitVec.Lemmas public import Init.Data.Int.Order import Init.ByCases import Init.Data.BitVec.Bitblast import Init.Data.BitVec.Bootstrap import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.UInt.Lemmas import Init.System.Platform
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "commandDeclare_int_theorems__"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__0 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 239, 52, 0, 96, 209, 11, 62)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__1 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__1_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__2 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__3 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "declare_int_theorems"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__4 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__5 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__5_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__6 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__7 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__8 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__5_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__9 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__9_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__10 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__11 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__12 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__9_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__13 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__14 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__int__theorems____ = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__14_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_iff_toBitVec_sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(224, 98, 156, 243, 176, 144, 13, 23)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↔"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.toBitVec.sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(229, 214, 5, 189, 16, 107, 180, 166)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "b.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 47, 200, 31, 68, 206, 165)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Iff.rfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(197, 85, 193, 93, 217, 248, 54, 49)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lt_iff_toBitVec_slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(7, 125, 217, 200, 188, 3, 210, 9)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.toBitVec.slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(216, 157, 226, 89, 27, 108, 130, 144)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(89, 245, 252, 212, 180, 248, 61, 129)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec.inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value),LEAN_SCALAR_PTR_LITERAL(3, 10, 226, 202, 47, 118, 47, 253)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_value),LEAN_SCALAR_PTR_LITERAL(169, 13, 108, 115, 152, 155, 29, 181)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "▸"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofBitVec_inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value),LEAN_SCALAR_PTR_LITERAL(221, 185, 57, 244, 153, 117, 189, 185)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(109, 13, 70, 115, 31, 141, 156, 173)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Iff.intro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value),LEAN_SCALAR_PTR_LITERAL(176, 155, 85, 49, 105, 137, 67, 168)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rintro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value),LEAN_SCALAR_PTR_LITERAL(170, 254, 242, 235, 94, 162, 254, 146)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rintroPat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value_aux_3),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value),LEAN_SCALAR_PTR_LITERAL(40, 214, 202, 122, 59, 249, 35, 61)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rcasesPat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_3),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value),LEAN_SCALAR_PTR_LITERAL(186, 152, 172, 228, 11, 240, 156, 168)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_iff_ofBitVec_eq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value),LEAN_SCALAR_PTR_LITERAL(204, 182, 120, 87, 208, 6, 5, 44)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ofBitVec_inj.symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value),LEAN_SCALAR_PTR_LITERAL(221, 185, 57, 244, 153, 117, 189, 185)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value),LEAN_SCALAR_PTR_LITERAL(22, 209, 90, 41, 119, 255, 106, 147)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_iff_ofBitVec_ne"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value),LEAN_SCALAR_PTR_LITERAL(177, 124, 199, 96, 100, 166, 4, 189)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≠_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value),LEAN_SCALAR_PTR_LITERAL(120, 22, 203, 44, 60, 124, 87, 95)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≠"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_iff_toBitVec_eq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value),LEAN_SCALAR_PTR_LITERAL(204, 196, 118, 25, 1, 164, 248, 180)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toBitVec_inj.symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(89, 245, 252, 212, 180, 248, 61, 129)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_value),LEAN_SCALAR_PTR_LITERAL(66, 49, 95, 225, 222, 165, 83, 187)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_iff_toBitVec_ne"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value),LEAN_SCALAR_PTR_LITERAL(166, 231, 164, 53, 49, 215, 3, 212)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Decidable.not_iff_not"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_iff_not"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_value),LEAN_SCALAR_PTR_LITERAL(72, 176, 176, 135, 176, 196, 69, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value),LEAN_SCALAR_PTR_LITERAL(167, 64, 108, 103, 216, 152, 33, 14)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toBitVec_ofNat'"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value),LEAN_SCALAR_PTR_LITERAL(16, 207, 149, 240, 11, 231, 225, 30)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value),LEAN_SCALAR_PTR_LITERAL(190, 214, 116, 82, 37, 136, 167, 32)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "BitVec.ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toBitVec_ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value),LEAN_SCALAR_PTR_LITERAL(48, 40, 156, 211, 194, 107, 54, 55)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noindex"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value),LEAN_SCALAR_PTR_LITERAL(0, 143, 63, 201, 38, 174, 32, 127)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no_index"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNat.ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value),LEAN_SCALAR_PTR_LITERAL(33, 80, 123, 180, 50, 194, 119, 199)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_add"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value),LEAN_SCALAR_PTR_LITERAL(54, 148, 186, 80, 123, 86, 181, 153)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_+_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value),LEAN_SCALAR_PTR_LITERAL(57, 160, 89, 154, 247, 230, 95, 119)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_sub"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value),LEAN_SCALAR_PTR_LITERAL(11, 9, 230, 95, 126, 235, 121, 31)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_-_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value),LEAN_SCALAR_PTR_LITERAL(92, 98, 183, 241, 65, 154, 192, 109)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_mul"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value),LEAN_SCALAR_PTR_LITERAL(78, 183, 160, 166, 105, 95, 150, 56)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_*_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value),LEAN_SCALAR_PTR_LITERAL(166, 30, 182, 203, 156, 152, 64, 201)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_div"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value),LEAN_SCALAR_PTR_LITERAL(237, 243, 123, 229, 238, 121, 75, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_/_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_value),LEAN_SCALAR_PTR_LITERAL(210, 175, 43, 55, 191, 201, 132, 176)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a.toBitVec.sdiv"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sdiv"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value),LEAN_SCALAR_PTR_LITERAL(12, 106, 63, 230, 239, 115, 94, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_mod"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value),LEAN_SCALAR_PTR_LITERAL(128, 222, 30, 228, 150, 168, 215, 197)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_%_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 140, 105, 32, 178, 232, 218)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a.toBitVec.srem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "srem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value),LEAN_SCALAR_PTR_LITERAL(106, 212, 48, 197, 204, 217, 39, 75)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Array_mkArray0(lean_box(0));
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23));
v___x_88_ = l_String_toRawSubstring_x27(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31));
v___x_106_ = l_String_toRawSubstring_x27(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39));
v___x_124_ = l_String_toRawSubstring_x27(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42));
v___x_129_ = l_String_toRawSubstring_x27(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57));
v___x_156_ = l_String_toRawSubstring_x27(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62));
v___x_165_ = l_String_toRawSubstring_x27(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68));
v___x_178_ = l_String_toRawSubstring_x27(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76));
v___x_193_ = l_String_toRawSubstring_x27(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82));
v___x_202_ = l_String_toRawSubstring_x27(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86));
v___x_210_ = l_String_toRawSubstring_x27(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91));
v___x_218_ = l_String_toRawSubstring_x27(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98));
v___x_232_ = l_String_toRawSubstring_x27(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110));
v___x_256_ = l_String_toRawSubstring_x27(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71));
v___x_272_ = l_String_toRawSubstring_x27(v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122));
v___x_279_ = l_String_toRawSubstring_x27(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125));
v___x_284_ = l_String_toRawSubstring_x27(v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128));
v___x_289_ = l_String_toRawSubstring_x27(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143));
v___x_326_ = l_String_toRawSubstring_x27(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156));
v___x_360_ = l_String_toRawSubstring_x27(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166));
v___x_384_ = l_String_toRawSubstring_x27(v___x_383_);
return v___x_384_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169));
v___x_389_ = l_String_toRawSubstring_x27(v___x_388_);
return v___x_389_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173));
v___x_396_ = l_String_toRawSubstring_x27(v___x_395_);
return v___x_396_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186));
v___x_424_ = l_String_toRawSubstring_x27(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189));
v___x_429_ = l_String_toRawSubstring_x27(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192));
v___x_435_ = l_String_toRawSubstring_x27(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197));
v___x_446_ = l_String_toRawSubstring_x27(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207));
v___x_464_ = l_String_toRawSubstring_x27(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210));
v___x_469_ = l_String_toRawSubstring_x27(v___x_468_);
return v___x_469_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213));
v___x_474_ = l_String_toRawSubstring_x27(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59));
v___x_478_ = l_String_toRawSubstring_x27(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218));
v___x_483_ = l_String_toRawSubstring_x27(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221));
v___x_488_ = l_String_toRawSubstring_x27(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227));
v___x_501_ = l_String_toRawSubstring_x27(v___x_500_);
return v___x_501_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233));
v___x_513_ = l_String_toRawSubstring_x27(v___x_512_);
return v___x_513_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239));
v___x_526_ = l_String_toRawSubstring_x27(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245));
v___x_535_ = l_String_toRawSubstring_x27(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251));
v___x_544_ = l_String_toRawSubstring_x27(v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257));
v___x_553_ = l_String_toRawSubstring_x27(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263));
v___x_562_ = l_String_toRawSubstring_x27(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267));
v___x_570_ = l_String_toRawSubstring_x27(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_578_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273));
v___x_579_ = l_String_toRawSubstring_x27(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(lean_object* v_x_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_594_; uint8_t v___x_595_; 
v___x_594_ = ((lean_object*)(l_commandDeclare__int__theorems_____00__closed__1));
lean_inc(v_x_591_);
v___x_595_ = l_Lean_Syntax_isOfKind(v_x_591_, v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_x_591_);
v___x_596_ = lean_box(1);
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v_a_593_);
return v___x_597_;
}
else
{
lean_object* v_ref_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_ref_598_ = lean_ctor_get(v_a_592_, 5);
v___x_599_ = lean_unsigned_to_nat(1u);
v___x_600_ = l_Lean_Syntax_getArg(v_x_591_, v___x_599_);
v___x_601_ = lean_unsigned_to_nat(2u);
v___x_602_ = l_Lean_Syntax_getArg(v_x_591_, v___x_601_);
lean_dec(v_x_591_);
v___x_603_ = 0;
v___x_604_ = l_Lean_SourceInfo_fromRef(v_ref_598_, v___x_603_);
v___x_605_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1));
v___x_606_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5));
v___x_607_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6));
lean_inc_n(v___x_604_, 306);
v___x_608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_604_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
lean_inc_n(v___x_600_, 2);
v___x_609_ = l_Lean_Syntax_node2(v___x_604_, v___x_607_, v___x_608_, v___x_600_);
v___x_610_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8));
v___x_611_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10));
v___x_612_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v___x_604_);
lean_ctor_set(v___x_613_, 1, v___x_605_);
lean_ctor_set(v___x_613_, 2, v___x_612_);
v___x_614_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14));
v___x_615_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15));
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_604_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17));
v___x_618_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19));
lean_inc_ref_n(v___x_613_, 70);
v___x_619_ = l_Lean_Syntax_node1(v___x_604_, v___x_618_, v___x_613_);
v___x_620_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22));
v___x_621_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24);
v___x_622_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25));
v___x_623_ = lean_box(0);
v___x_624_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_624_, 0, v___x_604_);
lean_ctor_set(v___x_624_, 1, v___x_621_);
lean_ctor_set(v___x_624_, 2, v___x_622_);
lean_ctor_set(v___x_624_, 3, v___x_623_);
v___x_625_ = l_Lean_Syntax_node2(v___x_604_, v___x_620_, v___x_624_, v___x_613_);
lean_inc(v___x_619_);
v___x_626_ = l_Lean_Syntax_node2(v___x_604_, v___x_617_, v___x_619_, v___x_625_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_626_);
v___x_628_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26));
v___x_629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_604_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
lean_inc_ref_n(v___x_629_, 3);
lean_inc_ref_n(v___x_616_, 2);
v___x_630_ = l_Lean_Syntax_node3(v___x_604_, v___x_614_, v___x_616_, v___x_627_, v___x_629_);
v___x_631_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_630_);
v___x_632_ = l_Lean_Syntax_node7(v___x_604_, v___x_611_, v___x_613_, v___x_631_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_);
v___x_633_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27));
v___x_634_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28));
v___x_635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_604_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
v___x_636_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30));
v___x_637_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32);
v___x_638_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33));
v___x_639_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_639_, 0, v___x_604_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_638_);
lean_ctor_set(v___x_639_, 3, v___x_623_);
v___x_640_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_639_, v___x_613_);
v___x_641_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35));
v___x_642_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37));
v___x_643_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38));
v___x_644_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_604_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
v___x_645_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40);
v___x_646_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41));
v___x_647_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_647_, 0, v___x_604_);
lean_ctor_set(v___x_647_, 1, v___x_645_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
lean_ctor_set(v___x_647_, 3, v___x_623_);
v___x_648_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43);
v___x_649_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44));
v___x_650_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_650_, 0, v___x_604_);
lean_ctor_set(v___x_650_, 1, v___x_648_);
lean_ctor_set(v___x_650_, 2, v___x_649_);
lean_ctor_set(v___x_650_, 3, v___x_623_);
lean_inc_ref_n(v___x_650_, 10);
lean_inc_ref_n(v___x_647_, 10);
v___x_651_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_647_, v___x_650_);
v___x_652_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45));
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_604_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
lean_inc_ref_n(v___x_653_, 17);
v___x_654_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_653_, v___x_600_);
v___x_655_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46));
v___x_656_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_604_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_inc_ref_n(v___x_656_, 2);
lean_inc(v___x_651_);
lean_inc_ref_n(v___x_644_, 2);
v___x_657_ = l_Lean_Syntax_node4(v___x_604_, v___x_642_, v___x_644_, v___x_651_, v___x_654_, v___x_656_);
v___x_658_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_657_);
v___x_659_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48));
v___x_660_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50));
v___x_661_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52));
v___x_662_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53));
v___x_663_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_604_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_Syntax_node3(v___x_604_, v___x_661_, v___x_647_, v___x_663_, v___x_650_);
v___x_665_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54));
v___x_666_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_604_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56));
v___x_668_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58);
v___x_669_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61));
v___x_670_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_670_, 0, v___x_604_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
lean_ctor_set(v___x_670_, 2, v___x_669_);
lean_ctor_set(v___x_670_, 3, v___x_623_);
v___x_671_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63);
v___x_672_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64));
v___x_673_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_673_, 0, v___x_604_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
lean_ctor_set(v___x_673_, 2, v___x_672_);
lean_ctor_set(v___x_673_, 3, v___x_623_);
lean_inc_ref_n(v___x_673_, 5);
v___x_674_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_673_);
lean_inc_n(v___x_674_, 3);
v___x_675_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_670_, v___x_674_);
lean_inc_ref_n(v___x_666_, 7);
v___x_676_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_664_, v___x_666_, v___x_675_);
v___x_677_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_676_);
lean_inc_n(v___x_658_, 9);
v___x_678_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_677_);
v___x_679_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66));
v___x_680_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67));
v___x_681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_604_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69);
v___x_683_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71));
v___x_684_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72));
v___x_685_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_685_, 0, v___x_604_);
lean_ctor_set(v___x_685_, 1, v___x_682_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
lean_ctor_set(v___x_685_, 3, v___x_623_);
v___x_686_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75));
v___x_687_ = l_Lean_Syntax_node2(v___x_604_, v___x_686_, v___x_613_, v___x_613_);
lean_inc_n(v___x_687_, 7);
lean_inc_ref_n(v___x_681_, 7);
v___x_688_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_685_, v___x_687_, v___x_613_);
lean_inc(v___x_688_);
lean_inc_ref_n(v___x_635_, 14);
v___x_689_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_640_, v___x_678_, v___x_688_);
lean_inc_n(v___x_632_, 3);
v___x_690_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_632_, v___x_689_);
v___x_691_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77);
v___x_692_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78));
v___x_693_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_693_, 0, v___x_604_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
lean_ctor_set(v___x_693_, 2, v___x_692_);
lean_ctor_set(v___x_693_, 3, v___x_623_);
v___x_694_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_693_, v___x_613_);
v___x_695_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80));
v___x_696_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_604_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_Syntax_node3(v___x_604_, v___x_695_, v___x_647_, v___x_697_, v___x_650_);
v___x_699_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83);
v___x_700_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85));
v___x_701_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_701_, 0, v___x_604_);
lean_ctor_set(v___x_701_, 1, v___x_699_);
lean_ctor_set(v___x_701_, 2, v___x_700_);
lean_ctor_set(v___x_701_, 3, v___x_623_);
v___x_702_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_701_, v___x_674_);
v___x_703_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_698_, v___x_666_, v___x_702_);
v___x_704_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_703_);
v___x_705_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_704_);
v___x_706_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_694_, v___x_705_, v___x_688_);
v___x_707_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_632_, v___x_706_);
v___x_708_ = l_Lean_Syntax_node7(v___x_604_, v___x_611_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_);
v___x_709_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87);
v___x_710_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88));
v___x_711_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_711_, 0, v___x_604_);
lean_ctor_set(v___x_711_, 1, v___x_709_);
lean_ctor_set(v___x_711_, 2, v___x_710_);
lean_ctor_set(v___x_711_, 3, v___x_623_);
v___x_712_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_711_, v___x_613_);
v___x_713_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90));
v___x_714_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92);
v___x_715_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93));
v___x_716_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_716_, 0, v___x_604_);
lean_ctor_set(v___x_716_, 1, v___x_714_);
lean_ctor_set(v___x_716_, 2, v___x_715_);
lean_ctor_set(v___x_716_, 3, v___x_623_);
v___x_717_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94));
v___x_718_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_604_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
lean_inc_ref_n(v___x_718_, 9);
lean_inc_ref_n(v___x_716_, 4);
v___x_719_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_716_, v___x_718_, v___x_673_);
v___x_720_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_647_, v___x_718_, v___x_650_);
lean_inc_n(v___x_720_, 3);
lean_inc(v___x_719_);
v___x_721_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_719_, v___x_666_, v___x_720_);
v___x_722_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_721_);
v___x_723_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_722_);
v___x_724_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96));
v___x_725_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97));
v___x_726_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_604_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99);
v___x_728_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101));
v___x_729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_729_, 0, v___x_604_);
lean_ctor_set(v___x_729_, 1, v___x_727_);
lean_ctor_set(v___x_729_, 2, v___x_728_);
lean_ctor_set(v___x_729_, 3, v___x_623_);
v___x_730_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102));
v___x_731_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_604_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104));
v___x_733_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106));
v___x_734_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107));
v___x_735_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_604_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109));
v___x_737_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111);
v___x_738_ = lean_box(0);
v___x_739_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_739_, 0, v___x_604_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
lean_ctor_set(v___x_739_, 3, v___x_623_);
v___x_740_ = l_Lean_Syntax_node1(v___x_604_, v___x_736_, v___x_739_);
lean_inc(v___x_740_);
lean_inc_ref(v___x_735_);
v___x_741_ = l_Lean_Syntax_node2(v___x_604_, v___x_733_, v___x_735_, v___x_740_);
v___x_742_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113));
v___x_743_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115));
v___x_744_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116));
v___x_745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_604_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = l_Lean_Syntax_node2(v___x_604_, v___x_743_, v___x_745_, v___x_740_);
v___x_747_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117));
v___x_748_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_604_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118);
v___x_750_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119));
v___x_751_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_751_, 0, v___x_604_);
lean_ctor_set(v___x_751_, 1, v___x_749_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
lean_ctor_set(v___x_751_, 3, v___x_623_);
lean_inc_ref(v___x_751_);
v___x_752_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_751_);
v___x_753_ = l_Lean_Syntax_node3(v___x_604_, v___x_742_, v___x_746_, v___x_748_, v___x_752_);
v___x_754_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120));
v___x_755_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_604_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
lean_inc_ref_n(v___x_755_, 10);
lean_inc_n(v___x_741_, 9);
v___x_756_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_753_, v___x_755_);
lean_inc_ref(v___x_731_);
v___x_757_ = l_Lean_Syntax_node3(v___x_604_, v___x_605_, v___x_729_, v___x_731_, v___x_756_);
v___x_758_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121));
v___x_759_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_604_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_Lean_Syntax_node3(v___x_604_, v___x_724_, v___x_726_, v___x_757_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_760_, v___x_687_, v___x_613_);
v___x_762_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_712_, v___x_723_, v___x_761_);
lean_inc_n(v___x_708_, 3);
v___x_763_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_708_, v___x_762_);
v___x_764_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123);
v___x_765_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124));
v___x_766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_766_, 0, v___x_604_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_ctor_set(v___x_766_, 3, v___x_623_);
lean_inc_ref(v___x_766_);
v___x_767_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_766_, v___x_613_);
v___x_768_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126);
v___x_769_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127));
v___x_770_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_770_, 0, v___x_604_);
lean_ctor_set(v___x_770_, 1, v___x_768_);
lean_ctor_set(v___x_770_, 2, v___x_769_);
lean_ctor_set(v___x_770_, 3, v___x_623_);
v___x_771_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_602_);
v___x_772_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_770_, v___x_771_);
v___x_773_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_653_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node4(v___x_604_, v___x_642_, v___x_644_, v___x_651_, v___x_773_, v___x_656_);
v___x_775_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_774_);
v___x_776_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129);
v___x_777_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130));
v___x_778_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_778_, 0, v___x_604_);
lean_ctor_set(v___x_778_, 1, v___x_776_);
lean_ctor_set(v___x_778_, 2, v___x_777_);
lean_ctor_set(v___x_778_, 3, v___x_623_);
v___x_779_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_647_);
lean_inc_ref(v___x_778_);
v___x_780_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_778_, v___x_779_);
v___x_781_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_650_);
v___x_782_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_778_, v___x_781_);
lean_inc(v___x_782_);
lean_inc(v___x_780_);
v___x_783_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_780_, v___x_718_, v___x_782_);
lean_inc(v___x_783_);
v___x_784_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_783_, v___x_666_, v___x_720_);
v___x_785_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_784_);
lean_inc_n(v___x_775_, 2);
v___x_786_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_775_, v___x_785_);
v___x_787_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132));
v___x_788_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133));
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_604_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136));
v___x_791_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138));
v___x_792_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140));
v___x_793_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141));
v___x_794_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142));
v___x_795_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_604_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
v___x_796_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144);
v___x_797_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146));
v___x_798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_798_, 0, v___x_604_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
lean_ctor_set(v___x_798_, 2, v___x_797_);
lean_ctor_set(v___x_798_, 3, v___x_623_);
v___x_799_ = l_Lean_Syntax_node2(v___x_604_, v___x_794_, v___x_795_, v___x_798_);
v___x_800_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147));
v___x_801_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_604_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148));
v___x_803_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149));
v___x_804_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_604_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
v___x_806_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153));
v___x_807_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155));
v___x_808_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157);
v___x_809_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158));
v___x_810_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_810_, 0, v___x_604_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_ctor_set(v___x_810_, 3, v___x_623_);
lean_inc_ref(v___x_810_);
v___x_811_ = l_Lean_Syntax_node1(v___x_604_, v___x_807_, v___x_810_);
v___x_812_ = l_Lean_Syntax_node1(v___x_604_, v___x_806_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_812_);
v___x_814_ = l_Lean_Syntax_node3(v___x_604_, v___x_804_, v___x_805_, v___x_813_, v___x_613_);
v___x_815_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159));
v___x_816_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_604_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160));
v___x_818_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161));
v___x_819_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_604_);
lean_ctor_set(v___x_819_, 1, v___x_817_);
v___x_820_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163));
v___x_821_ = l_Lean_Syntax_node2(v___x_604_, v___x_820_, v___x_613_, v___x_810_);
v___x_822_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node4(v___x_604_, v___x_818_, v___x_819_, v___x_822_, v___x_613_, v___x_613_);
v___x_824_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165));
v___x_825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_604_);
lean_ctor_set(v___x_825_, 1, v___x_683_);
v___x_826_ = l_Lean_Syntax_node1(v___x_604_, v___x_824_, v___x_825_);
lean_inc_ref(v___x_816_);
v___x_827_ = l_Lean_Syntax_node5(v___x_604_, v___x_605_, v___x_814_, v___x_816_, v___x_823_, v___x_816_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node1(v___x_604_, v___x_791_, v___x_827_);
v___x_829_ = l_Lean_Syntax_node1(v___x_604_, v___x_790_, v___x_828_);
v___x_830_ = l_Lean_Syntax_node3(v___x_604_, v___x_802_, v___x_735_, v___x_829_, v___x_755_);
v___x_831_ = l_Lean_Syntax_node3(v___x_604_, v___x_792_, v___x_799_, v___x_801_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_831_);
v___x_833_ = l_Lean_Syntax_node1(v___x_604_, v___x_791_, v___x_832_);
v___x_834_ = l_Lean_Syntax_node1(v___x_604_, v___x_790_, v___x_833_);
lean_inc_ref(v___x_789_);
v___x_835_ = l_Lean_Syntax_node2(v___x_604_, v___x_787_, v___x_789_, v___x_834_);
v___x_836_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_835_, v___x_687_, v___x_613_);
v___x_837_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_767_, v___x_786_, v___x_836_);
v___x_838_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_708_, v___x_837_);
v___x_839_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167);
v___x_840_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168));
v___x_841_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_841_, 0, v___x_604_);
lean_ctor_set(v___x_841_, 1, v___x_839_);
lean_ctor_set(v___x_841_, 2, v___x_840_);
lean_ctor_set(v___x_841_, 3, v___x_623_);
v___x_842_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_841_, v___x_613_);
v___x_843_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_720_, v___x_666_, v___x_783_);
v___x_844_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_843_);
v___x_845_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_775_, v___x_844_);
v___x_846_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170);
v___x_847_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172));
v___x_848_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_848_, 0, v___x_604_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
lean_ctor_set(v___x_848_, 2, v___x_847_);
lean_ctor_set(v___x_848_, 3, v___x_623_);
v___x_849_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_848_, v___x_687_, v___x_613_);
v___x_850_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_842_, v___x_845_, v___x_849_);
v___x_851_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_708_, v___x_850_);
v___x_852_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174);
v___x_853_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175));
v___x_854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_854_, 0, v___x_604_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_ctor_set(v___x_854_, 3, v___x_623_);
v___x_855_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_854_, v___x_613_);
v___x_856_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177));
v___x_857_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178));
v___x_858_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_604_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
lean_inc_ref_n(v___x_858_, 2);
v___x_859_ = l_Lean_Syntax_node3(v___x_604_, v___x_856_, v___x_647_, v___x_858_, v___x_650_);
v___x_860_ = l_Lean_Syntax_node3(v___x_604_, v___x_856_, v___x_780_, v___x_858_, v___x_782_);
lean_inc(v___x_859_);
v___x_861_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_859_, v___x_666_, v___x_860_);
v___x_862_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_861_);
v___x_863_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_775_, v___x_862_);
v___x_864_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179));
v___x_865_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180));
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_604_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
v___x_867_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182));
v___x_868_ = l_Lean_Syntax_node1(v___x_604_, v___x_867_, v___x_613_);
v___x_869_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183));
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_604_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185));
v___x_872_ = l_Lean_Syntax_node3(v___x_604_, v___x_871_, v___x_613_, v___x_613_, v___x_766_);
v___x_873_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_872_);
v___x_874_ = l_Lean_Syntax_node3(v___x_604_, v___x_605_, v___x_870_, v___x_873_, v___x_629_);
lean_inc_ref(v___x_866_);
v___x_875_ = l_Lean_Syntax_node6(v___x_604_, v___x_865_, v___x_866_, v___x_868_, v___x_613_, v___x_613_, v___x_874_, v___x_613_);
v___x_876_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node1(v___x_604_, v___x_791_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node1(v___x_604_, v___x_790_, v___x_877_);
v___x_879_ = l_Lean_Syntax_node2(v___x_604_, v___x_787_, v___x_789_, v___x_878_);
v___x_880_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_879_, v___x_687_, v___x_613_);
v___x_881_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_855_, v___x_863_, v___x_880_);
v___x_882_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_708_, v___x_881_);
v___x_883_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187);
v___x_884_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188));
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___x_604_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
lean_ctor_set(v___x_885_, 2, v___x_884_);
lean_ctor_set(v___x_885_, 3, v___x_623_);
lean_inc_ref(v___x_885_);
v___x_886_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_885_, v___x_613_);
v___x_887_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_720_, v___x_666_, v___x_719_);
v___x_888_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_887_);
v___x_889_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_888_);
v___x_890_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190);
v___x_891_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191));
v___x_892_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_892_, 0, v___x_604_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
lean_ctor_set(v___x_892_, 2, v___x_891_);
lean_ctor_set(v___x_892_, 3, v___x_623_);
v___x_893_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_892_, v___x_687_, v___x_613_);
v___x_894_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_886_, v___x_889_, v___x_893_);
v___x_895_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_632_, v___x_894_);
v___x_896_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193);
v___x_897_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194));
v___x_898_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_898_, 0, v___x_604_);
lean_ctor_set(v___x_898_, 1, v___x_896_);
lean_ctor_set(v___x_898_, 2, v___x_897_);
lean_ctor_set(v___x_898_, 3, v___x_623_);
v___x_899_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_898_, v___x_613_);
v___x_900_ = l_Lean_Syntax_node3(v___x_604_, v___x_856_, v___x_716_, v___x_858_, v___x_673_);
v___x_901_ = l_Lean_Syntax_node3(v___x_604_, v___x_660_, v___x_859_, v___x_666_, v___x_900_);
v___x_902_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_901_);
v___x_903_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_902_);
v___x_904_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196));
v___x_905_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198);
v___x_906_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201));
v___x_907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_907_, 0, v___x_604_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_ctor_set(v___x_907_, 3, v___x_623_);
v___x_908_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202));
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_604_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204));
v___x_911_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205));
v___x_912_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_604_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l_Lean_Syntax_node1(v___x_604_, v___x_910_, v___x_912_);
lean_inc_ref_n(v___x_909_, 5);
v___x_914_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_907_, v___x_909_, v___x_913_);
v___x_915_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_885_);
v___x_916_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_914_, v___x_915_);
v___x_917_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_916_, v___x_687_, v___x_613_);
v___x_918_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_899_, v___x_903_, v___x_917_);
v___x_919_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_632_, v___x_918_);
v___x_920_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206));
v___x_921_ = l_Lean_Syntax_node4(v___x_604_, v___x_920_, v___x_866_, v___x_613_, v___x_613_, v___x_613_);
v___x_922_ = l_Lean_Syntax_node2(v___x_604_, v___x_617_, v___x_619_, v___x_921_);
lean_inc(v___x_922_);
v___x_923_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_922_);
v___x_924_ = l_Lean_Syntax_node3(v___x_604_, v___x_614_, v___x_616_, v___x_923_, v___x_629_);
v___x_925_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_924_);
v___x_926_ = l_Lean_Syntax_node7(v___x_604_, v___x_611_, v___x_613_, v___x_925_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_);
v___x_927_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208);
v___x_928_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209));
v___x_929_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_929_, 0, v___x_604_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v___x_623_);
v___x_930_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_929_, v___x_613_);
v___x_931_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211);
v___x_932_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212));
v___x_933_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_933_, 0, v___x_604_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v___x_932_);
lean_ctor_set(v___x_933_, 3, v___x_623_);
lean_inc_ref(v___x_933_);
v___x_934_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_933_);
v___x_935_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214);
v___x_936_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215));
v___x_937_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_937_, 0, v___x_604_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
lean_ctor_set(v___x_937_, 2, v___x_936_);
lean_ctor_set(v___x_937_, 3, v___x_623_);
v___x_938_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_653_, v___x_937_);
lean_inc_n(v___x_934_, 2);
v___x_939_ = l_Lean_Syntax_node4(v___x_604_, v___x_642_, v___x_644_, v___x_934_, v___x_938_, v___x_656_);
v___x_940_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_939_);
v___x_941_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216);
v___x_942_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217));
v___x_943_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_943_, 0, v___x_604_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_942_);
lean_ctor_set(v___x_943_, 3, v___x_623_);
v___x_944_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219);
v___x_945_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220));
v___x_946_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_946_, 0, v___x_604_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
lean_ctor_set(v___x_946_, 3, v___x_623_);
v___x_947_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_946_, v___x_934_);
v___x_948_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_947_, v___x_755_);
v___x_949_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_948_);
lean_inc_ref_n(v___x_943_, 6);
v___x_950_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_943_, v___x_949_);
v___x_951_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222);
v___x_952_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223));
v___x_953_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_953_, 0, v___x_604_);
lean_ctor_set(v___x_953_, 1, v___x_951_);
lean_ctor_set(v___x_953_, 2, v___x_952_);
lean_ctor_set(v___x_953_, 3, v___x_623_);
v___x_954_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225));
v___x_955_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226));
v___x_956_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_604_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = l_Lean_Syntax_node1(v___x_604_, v___x_954_, v___x_956_);
v___x_958_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_957_, v___x_933_);
v___x_959_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_953_, v___x_958_);
v___x_960_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_950_, v___x_718_, v___x_959_);
v___x_961_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_960_);
lean_inc(v___x_940_);
v___x_962_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_940_, v___x_961_);
v___x_963_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_751_, v___x_755_);
v___x_964_ = l_Lean_Syntax_node4(v___x_604_, v___x_679_, v___x_681_, v___x_963_, v___x_687_, v___x_613_);
lean_inc_n(v___x_964_, 6);
v___x_965_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_930_, v___x_962_, v___x_964_);
v___x_966_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_926_, v___x_965_);
v___x_967_ = l_Lean_Syntax_node3(v___x_604_, v___x_605_, v___x_922_, v___x_731_, v___x_626_);
v___x_968_ = l_Lean_Syntax_node3(v___x_604_, v___x_614_, v___x_616_, v___x_967_, v___x_629_);
v___x_969_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_968_);
lean_inc(v___x_969_);
v___x_970_ = l_Lean_Syntax_node7(v___x_604_, v___x_611_, v___x_613_, v___x_969_, v___x_613_, v___x_613_, v___x_613_, v___x_613_, v___x_613_);
v___x_971_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228);
v___x_972_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229));
v___x_973_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_973_, 0, v___x_604_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
lean_ctor_set(v___x_973_, 3, v___x_623_);
v___x_974_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_973_, v___x_613_);
v___x_975_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231));
v___x_976_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232));
v___x_977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_604_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234);
v___x_979_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236));
v___x_980_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_980_, 0, v___x_604_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
lean_ctor_set(v___x_980_, 3, v___x_623_);
v___x_981_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_980_, v___x_934_);
lean_inc(v___x_981_);
v___x_982_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_981_, v___x_755_);
v___x_983_ = l_Lean_Syntax_node2(v___x_604_, v___x_975_, v___x_977_, v___x_982_);
v___x_984_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_983_, v___x_755_);
v___x_985_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_984_);
v___x_986_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_943_, v___x_985_);
v___x_987_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_986_, v___x_718_, v___x_981_);
v___x_988_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_987_);
v___x_989_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_940_, v___x_988_);
v___x_990_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_974_, v___x_989_, v___x_964_);
v___x_991_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_970_, v___x_990_);
v___x_992_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237));
v___x_993_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238));
v___x_994_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_604_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
v___x_995_ = l_Lean_Syntax_node1(v___x_604_, v___x_993_, v___x_994_);
v___x_996_ = l_Lean_Syntax_node1(v___x_604_, v___x_605_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node7(v___x_604_, v___x_611_, v___x_613_, v___x_969_, v___x_613_, v___x_996_, v___x_613_, v___x_613_, v___x_613_);
v___x_998_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240);
v___x_999_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241));
v___x_1000_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1000_, 0, v___x_604_);
lean_ctor_set(v___x_1000_, 1, v___x_998_);
lean_ctor_set(v___x_1000_, 2, v___x_999_);
lean_ctor_set(v___x_1000_, 3, v___x_623_);
v___x_1001_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_1000_, v___x_613_);
v___x_1002_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243));
v___x_1003_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244));
v___x_1004_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_604_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
lean_inc_ref(v___x_1004_);
v___x_1005_ = l_Lean_Syntax_node3(v___x_604_, v___x_1002_, v___x_647_, v___x_1004_, v___x_650_);
v___x_1006_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_1005_, v___x_755_);
v___x_1007_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_1006_, v___x_909_, v___x_943_);
v___x_1008_ = l_Lean_Syntax_node3(v___x_604_, v___x_1002_, v___x_716_, v___x_1004_, v___x_673_);
v___x_1009_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_1007_, v___x_718_, v___x_1008_);
v___x_1010_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_1010_);
v___x_1012_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_1001_, v___x_1011_, v___x_964_);
lean_inc_n(v___x_997_, 4);
v___x_1013_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_997_, v___x_1012_);
v___x_1014_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246);
v___x_1015_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247));
v___x_1016_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1016_, 0, v___x_604_);
lean_ctor_set(v___x_1016_, 1, v___x_1014_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_623_);
v___x_1017_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_1016_, v___x_613_);
v___x_1018_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249));
v___x_1019_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250));
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_604_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
lean_inc_ref(v___x_1020_);
v___x_1021_ = l_Lean_Syntax_node3(v___x_604_, v___x_1018_, v___x_647_, v___x_1020_, v___x_650_);
v___x_1022_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_1021_, v___x_755_);
v___x_1023_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_1022_, v___x_909_, v___x_943_);
v___x_1024_ = l_Lean_Syntax_node3(v___x_604_, v___x_1018_, v___x_716_, v___x_1020_, v___x_673_);
v___x_1025_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_1023_, v___x_718_, v___x_1024_);
v___x_1026_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_1026_);
v___x_1028_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_1017_, v___x_1027_, v___x_964_);
v___x_1029_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_997_, v___x_1028_);
v___x_1030_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252);
v___x_1031_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253));
v___x_1032_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1032_, 0, v___x_604_);
lean_ctor_set(v___x_1032_, 1, v___x_1030_);
lean_ctor_set(v___x_1032_, 2, v___x_1031_);
lean_ctor_set(v___x_1032_, 3, v___x_623_);
v___x_1033_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_1032_, v___x_613_);
v___x_1034_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255));
v___x_1035_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256));
v___x_1036_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_604_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
lean_inc_ref(v___x_1036_);
v___x_1037_ = l_Lean_Syntax_node3(v___x_604_, v___x_1034_, v___x_647_, v___x_1036_, v___x_650_);
v___x_1038_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_1037_, v___x_755_);
v___x_1039_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_1038_, v___x_909_, v___x_943_);
v___x_1040_ = l_Lean_Syntax_node3(v___x_604_, v___x_1034_, v___x_716_, v___x_1036_, v___x_673_);
v___x_1041_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_1039_, v___x_718_, v___x_1040_);
v___x_1042_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_1042_);
v___x_1044_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_1033_, v___x_1043_, v___x_964_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_997_, v___x_1044_);
v___x_1046_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258);
v___x_1047_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259));
v___x_1048_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1048_, 0, v___x_604_);
lean_ctor_set(v___x_1048_, 1, v___x_1046_);
lean_ctor_set(v___x_1048_, 2, v___x_1047_);
lean_ctor_set(v___x_1048_, 3, v___x_623_);
v___x_1049_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_1048_, v___x_613_);
v___x_1050_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261));
v___x_1051_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262));
v___x_1052_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_604_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = l_Lean_Syntax_node3(v___x_604_, v___x_1050_, v___x_647_, v___x_1052_, v___x_650_);
v___x_1054_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_1053_, v___x_755_);
v___x_1055_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_1054_, v___x_909_, v___x_943_);
v___x_1056_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264);
v___x_1057_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266));
v___x_1058_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1058_, 0, v___x_604_);
lean_ctor_set(v___x_1058_, 1, v___x_1056_);
lean_ctor_set(v___x_1058_, 2, v___x_1057_);
lean_ctor_set(v___x_1058_, 3, v___x_623_);
v___x_1059_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_1058_, v___x_674_);
v___x_1060_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_1055_, v___x_718_, v___x_1059_);
v___x_1061_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_1060_);
v___x_1062_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_1061_);
v___x_1063_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_1049_, v___x_1062_, v___x_964_);
v___x_1064_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_997_, v___x_1063_);
v___x_1065_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268);
v___x_1066_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269));
v___x_1067_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1067_, 0, v___x_604_);
lean_ctor_set(v___x_1067_, 1, v___x_1065_);
lean_ctor_set(v___x_1067_, 2, v___x_1066_);
lean_ctor_set(v___x_1067_, 3, v___x_623_);
v___x_1068_ = l_Lean_Syntax_node2(v___x_604_, v___x_636_, v___x_1067_, v___x_613_);
v___x_1069_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271));
v___x_1070_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272));
v___x_1071_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_604_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = l_Lean_Syntax_node3(v___x_604_, v___x_1069_, v___x_647_, v___x_1071_, v___x_650_);
v___x_1073_ = l_Lean_Syntax_node3(v___x_604_, v___x_732_, v___x_741_, v___x_1072_, v___x_755_);
v___x_1074_ = l_Lean_Syntax_node3(v___x_604_, v___x_904_, v___x_1073_, v___x_909_, v___x_943_);
v___x_1075_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274);
v___x_1076_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276));
v___x_1077_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1077_, 0, v___x_604_);
lean_ctor_set(v___x_1077_, 1, v___x_1075_);
lean_ctor_set(v___x_1077_, 2, v___x_1076_);
lean_ctor_set(v___x_1077_, 3, v___x_623_);
v___x_1078_ = l_Lean_Syntax_node2(v___x_604_, v___x_667_, v___x_1077_, v___x_674_);
v___x_1079_ = l_Lean_Syntax_node3(v___x_604_, v___x_713_, v___x_1074_, v___x_718_, v___x_1078_);
v___x_1080_ = l_Lean_Syntax_node2(v___x_604_, v___x_659_, v___x_653_, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_604_, v___x_641_, v___x_658_, v___x_1080_);
v___x_1082_ = l_Lean_Syntax_node4(v___x_604_, v___x_634_, v___x_635_, v___x_1068_, v___x_1081_, v___x_964_);
v___x_1083_ = l_Lean_Syntax_node2(v___x_604_, v___x_610_, v___x_997_, v___x_1082_);
v___x_1084_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277));
v___x_1085_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__278));
v___x_1086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_604_);
lean_ctor_set(v___x_1086_, 1, v___x_1084_);
v___x_1087_ = l_Lean_Syntax_node2(v___x_604_, v___x_605_, v___x_600_, v___x_613_);
v___x_1088_ = l_Lean_Syntax_node2(v___x_604_, v___x_1085_, v___x_1086_, v___x_1087_);
v___x_1089_ = lean_unsigned_to_nat(17u);
v___x_1090_ = lean_mk_empty_array_with_capacity(v___x_1089_);
v___x_1091_ = lean_array_push(v___x_1090_, v___x_609_);
v___x_1092_ = lean_array_push(v___x_1091_, v___x_690_);
v___x_1093_ = lean_array_push(v___x_1092_, v___x_707_);
v___x_1094_ = lean_array_push(v___x_1093_, v___x_763_);
v___x_1095_ = lean_array_push(v___x_1094_, v___x_838_);
v___x_1096_ = lean_array_push(v___x_1095_, v___x_851_);
v___x_1097_ = lean_array_push(v___x_1096_, v___x_882_);
v___x_1098_ = lean_array_push(v___x_1097_, v___x_895_);
v___x_1099_ = lean_array_push(v___x_1098_, v___x_919_);
v___x_1100_ = lean_array_push(v___x_1099_, v___x_966_);
v___x_1101_ = lean_array_push(v___x_1100_, v___x_991_);
v___x_1102_ = lean_array_push(v___x_1101_, v___x_1013_);
v___x_1103_ = lean_array_push(v___x_1102_, v___x_1029_);
v___x_1104_ = lean_array_push(v___x_1103_, v___x_1045_);
v___x_1105_ = lean_array_push(v___x_1104_, v___x_1064_);
v___x_1106_ = lean_array_push(v___x_1105_, v___x_1083_);
v___x_1107_ = lean_array_push(v___x_1106_, v___x_1088_);
v___x_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1108_, 0, v___x_604_);
lean_ctor_set(v___x_1108_, 1, v___x_605_);
lean_ctor_set(v___x_1108_, 2, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_getArgs(v___x_1108_);
lean_dec_ref(v___x_1108_);
v___x_1110_ = lean_box(2);
v___x_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_605_);
lean_ctor_set(v___x_1111_, 2, v___x_1109_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v_a_593_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___boxed(lean_object* v_x_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(v_x_1113_, v_a_1114_, v_a_1115_);
lean_dec_ref(v_a_1114_);
return v_res_1116_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
