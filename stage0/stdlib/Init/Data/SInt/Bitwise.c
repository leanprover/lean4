// Lean compiler output
// Module: Init.Data.SInt.Bitwise
// Imports: import all Init.Data.UInt.Basic import all Init.Data.BitVec.Basic import all Init.Data.BitVec.Lemmas import all Init.Data.SInt.Basic public import Init.Data.SInt.Basic public import Init.Ext import Init.Data.BitVec.Bitblast import Init.Data.SInt.Lemmas import Init.System.Platform
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_commandDeclare__bitwise__int__theorems_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "commandDeclare_bitwise_int_theorems__"};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__0 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 23, 191, 110, 65, 43, 96, 39)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__1 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__1_value;
static const lean_string_object l_commandDeclare__bitwise__int__theorems_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__2 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__3 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__3_value;
static const lean_string_object l_commandDeclare__bitwise__int__theorems_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "declare_bitwise_int_theorems"};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__4 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__5 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__5_value;
static const lean_string_object l_commandDeclare__bitwise__int__theorems_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__6 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__7 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__8 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__5_value),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__9 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__9_value;
static const lean_string_object l_commandDeclare__bitwise__int__theorems_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__10 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__11 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__12 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__9_value),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__13 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__bitwise__int__theorems_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__bitwise__int__theorems_____00__closed__14 = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__bitwise__int__theorems____ = (const lean_object*)&l_commandDeclare__bitwise__int__theorems_____00__closed__14_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(167, 64, 108, 103, 216, 152, 33, 14)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__24_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(33, 80, 123, 180, 50, 194, 119, 199)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_not"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(4, 183, 142, 241, 137, 246, 36, 132)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__39_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__49_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term~~~_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(77, 157, 31, 78, 77, 225, 98, 3)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "~~~"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__82_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_and"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85_value),LEAN_SCALAR_PTR_LITERAL(114, 9, 190, 33, 169, 157, 178, 61)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__88_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_&&&_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(193, 99, 184, 216, 31, 112, 180, 172)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "&&&"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "b.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 47, 200, 31, 68, 206, 165)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toBitVec_or"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99_value),LEAN_SCALAR_PTR_LITERAL(84, 192, 11, 42, 238, 76, 177, 131)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_|||_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__102_value),LEAN_SCALAR_PTR_LITERAL(235, 153, 6, 35, 60, 189, 128, 63)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|||"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_xor"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(134, 92, 36, 213, 197, 9, 127, 37)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_^^^_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(80, 193, 94, 25, 196, 159, 89, 59)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "^^^"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "toBitVec_shiftLeft"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(67, 94, 183, 134, 188, 119, 20, 251)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<<<_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(165, 87, 195, 47, 75, 199, 87, 179)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<<<"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "b.toBitVec.smod"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "smod"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 47, 200, 31, 68, 206, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__121_value),LEAN_SCALAR_PTR_LITERAL(40, 22, 211, 94, 185, 99, 127, 0)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "toBitVec_shiftRight"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123_value),LEAN_SCALAR_PTR_LITERAL(93, 43, 133, 175, 145, 37, 127, 56)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_>>>_"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__126_value),LEAN_SCALAR_PTR_LITERAL(42, 229, 82, 200, 78, 65, 60, 50)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">>>"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "a.toBitVec.sshiftRight'"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sshiftRight'"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__131_value),LEAN_SCALAR_PTR_LITERAL(239, 94, 99, 244, 171, 72, 235, 147)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_abs"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133_value),LEAN_SCALAR_PTR_LITERAL(2, 104, 147, 67, 55, 70, 103, 90)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.abs.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "abs"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value),LEAN_SCALAR_PTR_LITERAL(79, 24, 211, 250, 166, 8, 132, 9)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(38, 41, 28, 132, 151, 243, 114, 72)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.toBitVec.abs"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__138_value),LEAN_SCALAR_PTR_LITERAL(18, 100, 236, 57, 163, 250, 139, 64)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142_value;
static const lean_string_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144 = (const lean_object*)&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Array_mkArray0(lean_box(0));
return v___x_58_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__26));
v___x_95_ = l_String_toRawSubstring_x27(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__36));
v___x_119_ = l_String_toRawSubstring_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__44));
v___x_137_ = l_String_toRawSubstring_x27(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__62));
v___x_175_ = l_String_toRawSubstring_x27(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__69));
v___x_184_ = l_String_toRawSubstring_x27(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__73));
v___x_190_ = l_String_toRawSubstring_x27(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__79));
v___x_203_ = l_String_toRawSubstring_x27(v___x_202_);
return v___x_203_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__85));
v___x_215_ = l_String_toRawSubstring_x27(v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__90));
v___x_226_ = l_String_toRawSubstring_x27(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__96));
v___x_235_ = l_String_toRawSubstring_x27(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__99));
v___x_241_ = l_String_toRawSubstring_x27(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__105));
v___x_250_ = l_String_toRawSubstring_x27(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__111));
v___x_259_ = l_String_toRawSubstring_x27(v___x_258_);
return v___x_259_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__119));
v___x_274_ = l_String_toRawSubstring_x27(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__123));
v___x_282_ = l_String_toRawSubstring_x27(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__129));
v___x_291_ = l_String_toRawSubstring_x27(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__133));
v___x_299_ = l_String_toRawSubstring_x27(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__136));
v___x_304_ = l_String_toRawSubstring_x27(v___x_303_);
return v___x_304_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__140));
v___x_312_ = l_String_toRawSubstring_x27(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1(lean_object* v_x_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = ((lean_object*)(l_commandDeclare__bitwise__int__theorems_____00__closed__1));
lean_inc(v_x_323_);
v___x_327_ = l_Lean_Syntax_isOfKind(v_x_323_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_x_323_);
v___x_328_ = lean_box(1);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_325_);
return v___x_329_;
}
else
{
lean_object* v_ref_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_ref_330_ = lean_ctor_get(v_a_324_, 5);
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = l_Lean_Syntax_getArg(v_x_323_, v___x_331_);
v___x_333_ = lean_unsigned_to_nat(2u);
v___x_334_ = l_Lean_Syntax_getArg(v_x_323_, v___x_333_);
lean_dec(v_x_323_);
v___x_335_ = 0;
v___x_336_ = l_Lean_SourceInfo_fromRef(v_ref_330_, v___x_335_);
v___x_337_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__1));
v___x_338_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__5));
v___x_339_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__6));
lean_inc(v___x_336_);
v___x_340_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_336_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
lean_inc(v___x_332_);
lean_inc(v___x_336_);
v___x_341_ = l_Lean_Syntax_node2(v___x_336_, v___x_339_, v___x_340_, v___x_332_);
v___x_342_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__8));
v___x_343_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__10));
v___x_344_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__11);
lean_inc(v___x_336_);
v___x_345_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_336_);
lean_ctor_set(v___x_345_, 1, v___x_337_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
v___x_346_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__14));
v___x_347_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__15));
lean_inc(v___x_336_);
v___x_348_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_336_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__17));
v___x_350_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__19));
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_351_ = l_Lean_Syntax_node1(v___x_336_, v___x_350_, v___x_345_);
v___x_352_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__21));
v___x_353_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__22));
lean_inc(v___x_336_);
v___x_354_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_336_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_inc_ref_n(v___x_345_, 3);
lean_inc(v___x_336_);
v___x_355_ = l_Lean_Syntax_node4(v___x_336_, v___x_353_, v___x_354_, v___x_345_, v___x_345_, v___x_345_);
lean_inc(v___x_351_);
lean_inc(v___x_336_);
v___x_356_ = l_Lean_Syntax_node2(v___x_336_, v___x_349_, v___x_351_, v___x_355_);
v___x_357_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__23));
lean_inc(v___x_336_);
v___x_358_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_336_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
v___x_359_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__25));
v___x_360_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__27);
v___x_361_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__28));
v___x_362_ = lean_box(0);
lean_inc(v___x_336_);
v___x_363_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_363_, 0, v___x_336_);
lean_ctor_set(v___x_363_, 1, v___x_360_);
lean_ctor_set(v___x_363_, 2, v___x_361_);
lean_ctor_set(v___x_363_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_364_ = l_Lean_Syntax_node2(v___x_336_, v___x_359_, v___x_363_, v___x_345_);
lean_inc(v___x_336_);
v___x_365_ = l_Lean_Syntax_node2(v___x_336_, v___x_349_, v___x_351_, v___x_364_);
lean_inc(v___x_336_);
v___x_366_ = l_Lean_Syntax_node3(v___x_336_, v___x_337_, v___x_356_, v___x_358_, v___x_365_);
v___x_367_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__29));
lean_inc(v___x_336_);
v___x_368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_336_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
lean_inc(v___x_336_);
v___x_369_ = l_Lean_Syntax_node3(v___x_336_, v___x_346_, v___x_348_, v___x_366_, v___x_368_);
lean_inc(v___x_336_);
v___x_370_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_369_);
v___x_371_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__30));
v___x_372_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__31));
lean_inc(v___x_336_);
v___x_373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_336_);
lean_ctor_set(v___x_373_, 1, v___x_371_);
lean_inc(v___x_336_);
v___x_374_ = l_Lean_Syntax_node1(v___x_336_, v___x_372_, v___x_373_);
lean_inc(v___x_336_);
v___x_375_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_374_);
lean_inc_ref_n(v___x_345_, 5);
lean_inc(v___x_336_);
v___x_376_ = l_Lean_Syntax_node7(v___x_336_, v___x_343_, v___x_345_, v___x_370_, v___x_345_, v___x_375_, v___x_345_, v___x_345_, v___x_345_);
v___x_377_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__32));
v___x_378_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__33));
lean_inc(v___x_336_);
v___x_379_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_336_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
v___x_380_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__35));
v___x_381_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__37);
v___x_382_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__38));
lean_inc(v___x_336_);
v___x_383_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_383_, 0, v___x_336_);
lean_ctor_set(v___x_383_, 1, v___x_381_);
lean_ctor_set(v___x_383_, 2, v___x_382_);
lean_ctor_set(v___x_383_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_384_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_383_, v___x_345_);
v___x_385_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__40));
v___x_386_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__42));
v___x_387_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__43));
lean_inc(v___x_336_);
v___x_388_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_336_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__45);
v___x_390_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__46));
lean_inc(v___x_336_);
v___x_391_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_391_, 0, v___x_336_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_390_);
lean_ctor_set(v___x_391_, 3, v___x_362_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_392_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_391_);
v___x_393_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__47));
lean_inc(v___x_336_);
v___x_394_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_336_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
lean_inc(v___x_332_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_395_ = l_Lean_Syntax_node2(v___x_336_, v___x_337_, v___x_394_, v___x_332_);
v___x_396_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__48));
lean_inc(v___x_336_);
v___x_397_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_336_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
lean_inc(v___x_395_);
lean_inc(v___x_392_);
lean_inc(v___x_336_);
v___x_398_ = l_Lean_Syntax_node4(v___x_336_, v___x_386_, v___x_388_, v___x_392_, v___x_395_, v___x_397_);
lean_inc(v___x_336_);
v___x_399_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_398_);
v___x_400_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__50));
v___x_401_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__52));
v___x_402_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__54));
v___x_403_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__56));
v___x_404_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__58));
v___x_405_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__59));
lean_inc(v___x_336_);
v___x_406_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_406_, 0, v___x_336_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
v___x_407_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__61));
v___x_408_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__63);
v___x_409_ = lean_box(0);
lean_inc(v___x_336_);
v___x_410_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_410_, 0, v___x_336_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set(v___x_410_, 2, v___x_409_);
lean_ctor_set(v___x_410_, 3, v___x_362_);
lean_inc(v___x_336_);
v___x_411_ = l_Lean_Syntax_node1(v___x_336_, v___x_407_, v___x_410_);
lean_inc_ref(v___x_406_);
lean_inc(v___x_336_);
v___x_412_ = l_Lean_Syntax_node2(v___x_336_, v___x_404_, v___x_406_, v___x_411_);
v___x_413_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__65));
v___x_414_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__66));
lean_inc(v___x_336_);
v___x_415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_336_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
lean_inc_ref(v___x_391_);
lean_inc_ref(v___x_415_);
lean_inc(v___x_336_);
v___x_416_ = l_Lean_Syntax_node2(v___x_336_, v___x_413_, v___x_415_, v___x_391_);
v___x_417_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__67));
lean_inc(v___x_336_);
v___x_418_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_336_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_419_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_416_, v___x_418_);
v___x_420_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__68));
lean_inc(v___x_336_);
v___x_421_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_336_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__70);
v___x_423_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__71));
lean_inc(v___x_336_);
v___x_424_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_424_, 0, v___x_336_);
lean_ctor_set(v___x_424_, 1, v___x_422_);
lean_ctor_set(v___x_424_, 2, v___x_423_);
lean_ctor_set(v___x_424_, 3, v___x_362_);
lean_inc_ref(v___x_424_);
lean_inc_ref(v___x_421_);
lean_inc(v___x_336_);
v___x_425_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_419_, v___x_421_, v___x_424_);
v___x_426_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__72));
lean_inc(v___x_336_);
v___x_427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_336_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__74);
v___x_429_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__75));
lean_inc(v___x_336_);
v___x_430_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_430_, 0, v___x_336_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_429_);
lean_ctor_set(v___x_430_, 3, v___x_362_);
lean_inc_ref(v___x_430_);
lean_inc(v___x_336_);
v___x_431_ = l_Lean_Syntax_node2(v___x_336_, v___x_413_, v___x_415_, v___x_430_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_432_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_425_, v___x_427_, v___x_431_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_433_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_432_);
lean_inc(v___x_336_);
v___x_434_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_399_, v___x_433_);
v___x_435_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__77));
v___x_436_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__78));
lean_inc(v___x_336_);
v___x_437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_336_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__80);
v___x_439_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__81));
lean_inc(v___x_336_);
v___x_440_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_440_, 0, v___x_336_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
lean_ctor_set(v___x_440_, 3, v___x_362_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_441_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_440_, v___x_418_);
v___x_442_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__84));
lean_inc_ref_n(v___x_345_, 2);
lean_inc(v___x_336_);
v___x_443_ = l_Lean_Syntax_node2(v___x_336_, v___x_442_, v___x_345_, v___x_345_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_444_ = l_Lean_Syntax_node4(v___x_336_, v___x_435_, v___x_437_, v___x_441_, v___x_443_, v___x_345_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_445_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_384_, v___x_434_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_446_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_445_);
v___x_447_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__86);
v___x_448_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__87));
lean_inc(v___x_336_);
v___x_449_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_449_, 0, v___x_336_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
lean_ctor_set(v___x_449_, 2, v___x_448_);
lean_ctor_set(v___x_449_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_450_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_449_, v___x_345_);
v___x_451_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__89));
v___x_452_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__91);
v___x_453_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__92));
lean_inc(v___x_336_);
v___x_454_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_454_, 0, v___x_336_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
lean_ctor_set(v___x_454_, 2, v___x_453_);
lean_ctor_set(v___x_454_, 3, v___x_362_);
lean_inc_ref(v___x_454_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_455_ = l_Lean_Syntax_node2(v___x_336_, v___x_337_, v___x_391_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_395_);
lean_inc_ref(v___x_406_);
lean_inc(v___x_336_);
v___x_456_ = l_Lean_Syntax_node5(v___x_336_, v___x_451_, v___x_406_, v___x_455_, v___x_395_, v___x_345_, v___x_418_);
lean_inc(v___x_336_);
v___x_457_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_456_);
v___x_458_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__94));
v___x_459_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__95));
lean_inc(v___x_336_);
v___x_460_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_336_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
lean_inc_ref(v___x_454_);
lean_inc_ref(v___x_460_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_461_ = l_Lean_Syntax_node3(v___x_336_, v___x_458_, v___x_391_, v___x_460_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_462_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_461_, v___x_418_);
lean_inc_ref(v___x_424_);
lean_inc_ref(v___x_421_);
lean_inc(v___x_336_);
v___x_463_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_462_, v___x_421_, v___x_424_);
v___x_464_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__97);
v___x_465_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__98));
lean_inc(v___x_336_);
v___x_466_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_466_, 0, v___x_336_);
lean_ctor_set(v___x_466_, 1, v___x_464_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_ctor_set(v___x_466_, 3, v___x_362_);
lean_inc_ref(v___x_466_);
lean_inc_ref(v___x_430_);
lean_inc(v___x_336_);
v___x_467_ = l_Lean_Syntax_node3(v___x_336_, v___x_458_, v___x_430_, v___x_460_, v___x_466_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_468_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_463_, v___x_427_, v___x_467_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_469_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_468_);
lean_inc(v___x_457_);
lean_inc(v___x_336_);
v___x_470_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_457_, v___x_469_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_471_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_450_, v___x_470_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_472_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_471_);
v___x_473_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__100);
v___x_474_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__101));
lean_inc(v___x_336_);
v___x_475_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_475_, 0, v___x_336_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
lean_ctor_set(v___x_475_, 2, v___x_474_);
lean_ctor_set(v___x_475_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_476_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_475_, v___x_345_);
v___x_477_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__103));
v___x_478_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__104));
lean_inc(v___x_336_);
v___x_479_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_336_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_inc_ref(v___x_454_);
lean_inc_ref(v___x_479_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_480_ = l_Lean_Syntax_node3(v___x_336_, v___x_477_, v___x_391_, v___x_479_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_481_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_480_, v___x_418_);
lean_inc_ref(v___x_424_);
lean_inc_ref(v___x_421_);
lean_inc(v___x_336_);
v___x_482_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_481_, v___x_421_, v___x_424_);
lean_inc_ref(v___x_466_);
lean_inc_ref(v___x_430_);
lean_inc(v___x_336_);
v___x_483_ = l_Lean_Syntax_node3(v___x_336_, v___x_477_, v___x_430_, v___x_479_, v___x_466_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_484_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_482_, v___x_427_, v___x_483_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_485_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_484_);
lean_inc(v___x_457_);
lean_inc(v___x_336_);
v___x_486_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_457_, v___x_485_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_487_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_476_, v___x_486_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_488_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_487_);
v___x_489_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__106);
v___x_490_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__107));
lean_inc(v___x_336_);
v___x_491_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_491_, 0, v___x_336_);
lean_ctor_set(v___x_491_, 1, v___x_489_);
lean_ctor_set(v___x_491_, 2, v___x_490_);
lean_ctor_set(v___x_491_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_492_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_491_, v___x_345_);
v___x_493_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__109));
v___x_494_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__110));
lean_inc(v___x_336_);
v___x_495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_336_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
lean_inc_ref(v___x_454_);
lean_inc_ref(v___x_495_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_496_ = l_Lean_Syntax_node3(v___x_336_, v___x_493_, v___x_391_, v___x_495_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_497_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_496_, v___x_418_);
lean_inc_ref(v___x_424_);
lean_inc_ref(v___x_421_);
lean_inc(v___x_336_);
v___x_498_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_497_, v___x_421_, v___x_424_);
lean_inc_ref(v___x_430_);
lean_inc(v___x_336_);
v___x_499_ = l_Lean_Syntax_node3(v___x_336_, v___x_493_, v___x_430_, v___x_495_, v___x_466_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_500_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_498_, v___x_427_, v___x_499_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_501_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_500_);
lean_inc(v___x_457_);
lean_inc(v___x_336_);
v___x_502_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_457_, v___x_501_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_503_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_492_, v___x_502_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_504_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_503_);
v___x_505_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__112);
v___x_506_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__113));
lean_inc(v___x_336_);
v___x_507_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_507_, 0, v___x_336_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_ctor_set(v___x_507_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_508_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_507_, v___x_345_);
v___x_509_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__115));
v___x_510_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__116));
lean_inc(v___x_336_);
v___x_511_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_336_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
lean_inc_ref(v___x_454_);
lean_inc_ref(v___x_511_);
lean_inc_ref(v___x_391_);
lean_inc(v___x_336_);
v___x_512_ = l_Lean_Syntax_node3(v___x_336_, v___x_509_, v___x_391_, v___x_511_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_513_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_512_, v___x_418_);
lean_inc_ref(v___x_424_);
lean_inc_ref(v___x_421_);
lean_inc(v___x_336_);
v___x_514_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_513_, v___x_421_, v___x_424_);
v___x_515_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__118));
v___x_516_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__120);
v___x_517_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__122));
lean_inc(v___x_336_);
v___x_518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_518_, 0, v___x_336_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
lean_ctor_set(v___x_518_, 3, v___x_362_);
lean_inc(v___x_336_);
v___x_519_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_334_);
lean_inc(v___x_336_);
v___x_520_ = l_Lean_Syntax_node2(v___x_336_, v___x_515_, v___x_518_, v___x_519_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_412_);
lean_inc(v___x_336_);
v___x_521_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_520_, v___x_418_);
lean_inc(v___x_521_);
lean_inc(v___x_336_);
v___x_522_ = l_Lean_Syntax_node3(v___x_336_, v___x_509_, v___x_430_, v___x_511_, v___x_521_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_523_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_514_, v___x_427_, v___x_522_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_524_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_523_);
lean_inc(v___x_457_);
lean_inc(v___x_336_);
v___x_525_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_457_, v___x_524_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_526_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_508_, v___x_525_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_527_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_526_);
v___x_528_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__124);
v___x_529_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__125));
lean_inc(v___x_336_);
v___x_530_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_530_, 0, v___x_336_);
lean_ctor_set(v___x_530_, 1, v___x_528_);
lean_ctor_set(v___x_530_, 2, v___x_529_);
lean_ctor_set(v___x_530_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_531_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_530_, v___x_345_);
v___x_532_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__127));
v___x_533_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__128));
lean_inc(v___x_336_);
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_336_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
lean_inc(v___x_336_);
v___x_535_ = l_Lean_Syntax_node3(v___x_336_, v___x_532_, v___x_391_, v___x_534_, v___x_454_);
lean_inc_ref(v___x_418_);
lean_inc(v___x_336_);
v___x_536_ = l_Lean_Syntax_node3(v___x_336_, v___x_403_, v___x_412_, v___x_535_, v___x_418_);
lean_inc(v___x_336_);
v___x_537_ = l_Lean_Syntax_node3(v___x_336_, v___x_402_, v___x_536_, v___x_421_, v___x_424_);
v___x_538_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__130);
v___x_539_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__132));
lean_inc(v___x_336_);
v___x_540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_540_, 0, v___x_336_);
lean_ctor_set(v___x_540_, 1, v___x_538_);
lean_ctor_set(v___x_540_, 2, v___x_539_);
lean_ctor_set(v___x_540_, 3, v___x_362_);
lean_inc(v___x_336_);
v___x_541_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_521_);
lean_inc(v___x_336_);
v___x_542_ = l_Lean_Syntax_node2(v___x_336_, v___x_515_, v___x_540_, v___x_541_);
lean_inc_ref(v___x_427_);
lean_inc(v___x_336_);
v___x_543_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_537_, v___x_427_, v___x_542_);
lean_inc_ref(v___x_394_);
lean_inc(v___x_336_);
v___x_544_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_543_);
lean_inc(v___x_336_);
v___x_545_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_457_, v___x_544_);
lean_inc(v___x_444_);
lean_inc_ref(v___x_379_);
lean_inc(v___x_336_);
v___x_546_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_531_, v___x_545_, v___x_444_);
lean_inc(v___x_376_);
lean_inc(v___x_336_);
v___x_547_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_546_);
v___x_548_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__134);
v___x_549_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__135));
lean_inc(v___x_336_);
v___x_550_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_550_, 0, v___x_336_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
lean_ctor_set(v___x_550_, 3, v___x_362_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_551_ = l_Lean_Syntax_node2(v___x_336_, v___x_380_, v___x_550_, v___x_345_);
lean_inc_ref(v___x_345_);
lean_inc(v___x_336_);
v___x_552_ = l_Lean_Syntax_node5(v___x_336_, v___x_451_, v___x_406_, v___x_392_, v___x_395_, v___x_345_, v___x_418_);
lean_inc(v___x_336_);
v___x_553_ = l_Lean_Syntax_node1(v___x_336_, v___x_337_, v___x_552_);
v___x_554_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__137);
v___x_555_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__139));
lean_inc(v___x_336_);
v___x_556_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_556_, 0, v___x_336_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
lean_ctor_set(v___x_556_, 2, v___x_555_);
lean_ctor_set(v___x_556_, 3, v___x_362_);
v___x_557_ = lean_obj_once(&l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141, &l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141_once, _init_l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__141);
v___x_558_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__142));
lean_inc(v___x_336_);
v___x_559_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_559_, 0, v___x_336_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
lean_ctor_set(v___x_559_, 3, v___x_362_);
lean_inc(v___x_336_);
v___x_560_ = l_Lean_Syntax_node3(v___x_336_, v___x_401_, v___x_556_, v___x_427_, v___x_559_);
lean_inc(v___x_336_);
v___x_561_ = l_Lean_Syntax_node2(v___x_336_, v___x_400_, v___x_394_, v___x_560_);
lean_inc(v___x_336_);
v___x_562_ = l_Lean_Syntax_node2(v___x_336_, v___x_385_, v___x_553_, v___x_561_);
lean_inc(v___x_336_);
v___x_563_ = l_Lean_Syntax_node4(v___x_336_, v___x_378_, v___x_379_, v___x_551_, v___x_562_, v___x_444_);
lean_inc(v___x_336_);
v___x_564_ = l_Lean_Syntax_node2(v___x_336_, v___x_342_, v___x_376_, v___x_563_);
v___x_565_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__143));
v___x_566_ = ((lean_object*)(l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___closed__144));
lean_inc(v___x_336_);
v___x_567_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_336_);
lean_ctor_set(v___x_567_, 1, v___x_565_);
lean_inc(v___x_336_);
v___x_568_ = l_Lean_Syntax_node2(v___x_336_, v___x_337_, v___x_332_, v___x_345_);
lean_inc(v___x_336_);
v___x_569_ = l_Lean_Syntax_node2(v___x_336_, v___x_566_, v___x_567_, v___x_568_);
v___x_570_ = lean_unsigned_to_nat(9u);
v___x_571_ = lean_mk_empty_array_with_capacity(v___x_570_);
v___x_572_ = lean_array_push(v___x_571_, v___x_341_);
v___x_573_ = lean_array_push(v___x_572_, v___x_446_);
v___x_574_ = lean_array_push(v___x_573_, v___x_472_);
v___x_575_ = lean_array_push(v___x_574_, v___x_488_);
v___x_576_ = lean_array_push(v___x_575_, v___x_504_);
v___x_577_ = lean_array_push(v___x_576_, v___x_527_);
v___x_578_ = lean_array_push(v___x_577_, v___x_547_);
v___x_579_ = lean_array_push(v___x_578_, v___x_564_);
v___x_580_ = lean_array_push(v___x_579_, v___x_569_);
v___x_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_581_, 0, v___x_336_);
lean_ctor_set(v___x_581_, 1, v___x_337_);
lean_ctor_set(v___x_581_, 2, v___x_580_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v_a_325_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1___boxed(lean_object* v_x_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___aux__Init__Data__SInt__Bitwise______macroRules__commandDeclare__bitwise__int__theorems______1(v_x_583_, v_a_584_, v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_586_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Bitwise(builtin);
}
#ifdef __cplusplus
}
#endif
