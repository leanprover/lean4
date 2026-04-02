// Lean compiler output
// Module: Init.Data.Array.Mem
// Imports: public import Init.Data.Array.Basic public import Init.WFTactics import Init.Data.List.BasicAux import Init.Data.Nat.Linear meta import Init.MetaTypes
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_tacticArray__get__dec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Array_tacticArray__get__dec___closed__0 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__0_value;
static const lean_string_object l_Array_tacticArray__get__dec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "tacticArray_get_dec"};
static const lean_object* l_Array_tacticArray__get__dec___closed__1 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__1_value;
static const lean_ctor_object l_Array_tacticArray__get__dec___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_tacticArray__get__dec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_tacticArray__get__dec___closed__2_value_aux_0),((lean_object*)&l_Array_tacticArray__get__dec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(3, 8, 85, 220, 129, 64, 220, 113)}};
static const lean_object* l_Array_tacticArray__get__dec___closed__2 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__2_value;
static const lean_string_object l_Array_tacticArray__get__dec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "array_get_dec"};
static const lean_object* l_Array_tacticArray__get__dec___closed__3 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__3_value;
static const lean_ctor_object l_Array_tacticArray__get__dec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Array_tacticArray__get__dec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Array_tacticArray__get__dec___closed__4 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__4_value;
static const lean_ctor_object l_Array_tacticArray__get__dec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_tacticArray__get__dec___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__4_value)}};
static const lean_object* l_Array_tacticArray__get__dec___closed__5 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__5_value;
LEAN_EXPORT const lean_object* l_Array_tacticArray__get__dec = (const lean_object*)&l_Array_tacticArray__get__dec___closed__5_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Nat.lt_of_lt_of_le"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_lt_of_le"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(6, 233, 240, 89, 98, 17, 244, 226)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__33_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__39_value)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "sizeOf_get"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(164, 116, 245, 12, 236, 49, 175, 44)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(214, 254, 153, 200, 224, 189, 233, 233)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__45_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__46_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ellipsis"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(101, 52, 71, 179, 21, 116, 195, 217)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "sizeOf_getElem"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(249, 170, 156, 91, 74, 49, 36, 193)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(171, 197, 174, 237, 179, 246, 179, 225)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__69_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__70_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_tacticArray__mem__dec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "tacticArray_mem_dec"};
static const lean_object* l_Array_tacticArray__mem__dec___closed__0 = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__0_value;
static const lean_ctor_object l_Array_tacticArray__mem__dec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array_tacticArray__mem__dec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_tacticArray__mem__dec___closed__1_value_aux_0),((lean_object*)&l_Array_tacticArray__mem__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 62, 229, 7, 243, 133, 186, 9)}};
static const lean_object* l_Array_tacticArray__mem__dec___closed__1 = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__1_value;
static const lean_string_object l_Array_tacticArray__mem__dec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "array_mem_dec"};
static const lean_object* l_Array_tacticArray__mem__dec___closed__2 = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__2_value;
static const lean_ctor_object l_Array_tacticArray__mem__dec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Array_tacticArray__mem__dec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Array_tacticArray__mem__dec___closed__3 = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__3_value;
static const lean_ctor_object l_Array_tacticArray__mem__dec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_tacticArray__mem__dec___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Array_tacticArray__mem__dec___closed__3_value)}};
static const lean_object* l_Array_tacticArray__mem__dec___closed__4 = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__4_value;
LEAN_EXPORT const lean_object* l_Array_tacticArray__mem__dec = (const lean_object*)&l_Array_tacticArray__mem__dec___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Array.sizeOf_lt_of_mem"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "sizeOf_lt_of_mem"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_tacticArray__get__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(156, 36, 177, 20, 13, 141, 118, 58)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value;
static lean_once_cell_t l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(134, 21, 185, 205, 238, 88, 7, 106)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value;
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22_value;
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25));
v___x_72_ = l_String_toRawSubstring_x27(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37));
v___x_100_ = l_String_toRawSubstring_x27(v___x_99_);
return v___x_100_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42));
v___x_110_ = l_String_toRawSubstring_x27(v___x_109_);
return v___x_110_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62));
v___x_158_ = l_String_toRawSubstring_x27(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Array_mkArray0(lean_box(0));
return v___x_161_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66));
v___x_164_ = l_String_toRawSubstring_x27(v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Array_tacticArray__get__dec___closed__2));
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(1);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v_quotContext_183_; lean_object* v_currMacroScope_184_; lean_object* v_ref_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_quotContext_183_ = lean_ctor_get(v_a_177_, 1);
v_currMacroScope_184_ = lean_ctor_get(v_a_177_, 2);
v_ref_185_ = lean_ctor_get(v_a_177_, 5);
v___x_186_ = 0;
v___x_187_ = l_Lean_SourceInfo_fromRef(v_ref_185_, v___x_186_);
v___x_188_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3));
v___x_189_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4));
lean_inc_n(v___x_187_, 60);
v___x_190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_187_);
lean_ctor_set(v___x_190_, 1, v___x_188_);
v___x_191_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6));
v___x_192_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8));
v___x_193_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9));
v___x_194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_187_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
v___x_195_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11));
v___x_196_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13));
v___x_197_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15));
v___x_198_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16));
v___x_199_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_187_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18));
v___x_201_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19));
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_187_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20));
v___x_204_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21));
v___x_205_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_187_);
lean_ctor_set(v___x_205_, 1, v___x_203_);
v___x_206_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24));
v___x_207_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
v___x_208_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29));
lean_inc_n(v_currMacroScope_184_, 5);
lean_inc_n(v_quotContext_183_, 5);
v___x_209_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_208_, v_currMacroScope_184_);
v___x_210_ = lean_box(0);
v___x_211_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31));
v___x_212_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_212_, 0, v___x_187_);
lean_ctor_set(v___x_212_, 1, v___x_207_);
lean_ctor_set(v___x_212_, 2, v___x_209_);
lean_ctor_set(v___x_212_, 3, v___x_211_);
v___x_213_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32));
v___x_214_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34));
v___x_215_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36));
v___x_216_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
v___x_217_ = lean_box(0);
v___x_218_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_217_, v_currMacroScope_184_);
v___x_219_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41));
v___x_220_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_220_, 0, v___x_187_);
lean_ctor_set(v___x_220_, 1, v___x_216_);
lean_ctor_set(v___x_220_, 2, v___x_218_);
lean_ctor_set(v___x_220_, 3, v___x_219_);
v___x_221_ = l_Lean_Syntax_node1(v___x_187_, v___x_215_, v___x_220_);
lean_inc_ref_n(v___x_199_, 2);
v___x_222_ = l_Lean_Syntax_node2(v___x_187_, v___x_214_, v___x_199_, v___x_221_);
v___x_223_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43);
v___x_224_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44));
v___x_225_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_224_, v_currMacroScope_184_);
v___x_226_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47));
v___x_227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_227_, 0, v___x_187_);
lean_ctor_set(v___x_227_, 1, v___x_223_);
lean_ctor_set(v___x_227_, 2, v___x_225_);
lean_ctor_set(v___x_227_, 3, v___x_226_);
v___x_228_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49));
v___x_229_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50));
v___x_230_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_187_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_Syntax_node1(v___x_187_, v___x_228_, v___x_230_);
v___x_232_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_231_);
lean_inc(v___x_232_);
v___x_233_ = l_Lean_Syntax_node2(v___x_187_, v___x_206_, v___x_227_, v___x_232_);
v___x_234_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51));
v___x_235_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_187_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
lean_inc_ref_n(v___x_235_, 3);
lean_inc(v___x_222_);
v___x_236_ = l_Lean_Syntax_node3(v___x_187_, v___x_213_, v___x_222_, v___x_233_, v___x_235_);
v___x_237_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_236_);
lean_inc_ref(v___x_212_);
v___x_238_ = l_Lean_Syntax_node2(v___x_187_, v___x_206_, v___x_212_, v___x_237_);
lean_inc_ref(v___x_205_);
v___x_239_ = l_Lean_Syntax_node2(v___x_187_, v___x_204_, v___x_205_, v___x_238_);
v___x_240_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_239_);
v___x_241_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_240_);
v___x_242_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_241_);
lean_inc_ref(v___x_202_);
v___x_243_ = l_Lean_Syntax_node2(v___x_187_, v___x_200_, v___x_202_, v___x_242_);
v___x_244_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_243_);
v___x_245_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_244_);
v___x_246_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_245_);
v___x_247_ = l_Lean_Syntax_node3(v___x_187_, v___x_197_, v___x_199_, v___x_246_, v___x_235_);
v___x_248_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52));
v___x_249_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_187_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53));
v___x_251_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54));
v___x_252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_187_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
v___x_253_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56));
v___x_254_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58));
v___x_255_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60));
v___x_256_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61));
v___x_257_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_187_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
v___x_259_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64));
v___x_260_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_259_, v_currMacroScope_184_);
v___x_261_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_261_, 0, v___x_187_);
lean_ctor_set(v___x_261_, 1, v___x_258_);
lean_ctor_set(v___x_261_, 2, v___x_260_);
lean_ctor_set(v___x_261_, 3, v___x_210_);
v___x_262_ = l_Lean_Syntax_node2(v___x_187_, v___x_255_, v___x_257_, v___x_261_);
v___x_263_ = l_Lean_Syntax_node1(v___x_187_, v___x_254_, v___x_262_);
v___x_264_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_263_);
v___x_265_ = l_Lean_Syntax_node1(v___x_187_, v___x_253_, v___x_264_);
v___x_266_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_187_);
lean_ctor_set(v___x_267_, 1, v___x_191_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc_ref_n(v___x_267_, 3);
v___x_268_ = l_Lean_Syntax_node6(v___x_187_, v___x_251_, v___x_252_, v___x_265_, v___x_267_, v___x_267_, v___x_267_, v___x_267_);
lean_inc(v___x_268_);
lean_inc_ref(v___x_249_);
v___x_269_ = l_Lean_Syntax_node3(v___x_187_, v___x_191_, v___x_247_, v___x_249_, v___x_268_);
v___x_270_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_269_);
v___x_271_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_270_);
lean_inc_ref(v___x_194_);
v___x_272_ = l_Lean_Syntax_node2(v___x_187_, v___x_192_, v___x_194_, v___x_271_);
v___x_273_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67);
v___x_274_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68));
v___x_275_ = l_Lean_addMacroScope(v_quotContext_183_, v___x_274_, v_currMacroScope_184_);
v___x_276_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71));
v___x_277_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_277_, 0, v___x_187_);
lean_ctor_set(v___x_277_, 1, v___x_273_);
lean_ctor_set(v___x_277_, 2, v___x_275_);
lean_ctor_set(v___x_277_, 3, v___x_276_);
v___x_278_ = l_Lean_Syntax_node2(v___x_187_, v___x_206_, v___x_277_, v___x_232_);
v___x_279_ = l_Lean_Syntax_node3(v___x_187_, v___x_213_, v___x_222_, v___x_278_, v___x_235_);
v___x_280_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_279_);
v___x_281_ = l_Lean_Syntax_node2(v___x_187_, v___x_206_, v___x_212_, v___x_280_);
v___x_282_ = l_Lean_Syntax_node2(v___x_187_, v___x_204_, v___x_205_, v___x_281_);
v___x_283_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_282_);
v___x_284_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_283_);
v___x_285_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_284_);
v___x_286_ = l_Lean_Syntax_node2(v___x_187_, v___x_200_, v___x_202_, v___x_285_);
v___x_287_ = l_Lean_Syntax_node1(v___x_187_, v___x_191_, v___x_286_);
v___x_288_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_287_);
v___x_289_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_288_);
v___x_290_ = l_Lean_Syntax_node3(v___x_187_, v___x_197_, v___x_199_, v___x_289_, v___x_235_);
v___x_291_ = l_Lean_Syntax_node3(v___x_187_, v___x_191_, v___x_290_, v___x_249_, v___x_268_);
v___x_292_ = l_Lean_Syntax_node1(v___x_187_, v___x_196_, v___x_291_);
v___x_293_ = l_Lean_Syntax_node1(v___x_187_, v___x_195_, v___x_292_);
v___x_294_ = l_Lean_Syntax_node2(v___x_187_, v___x_192_, v___x_194_, v___x_293_);
v___x_295_ = l_Lean_Syntax_node2(v___x_187_, v___x_191_, v___x_272_, v___x_294_);
v___x_296_ = l_Lean_Syntax_node2(v___x_187_, v___x_189_, v___x_190_, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_a_178_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___boxed(lean_object* v_x_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(v_x_298_, v_a_299_, v_a_300_);
lean_dec_ref(v_a_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_box(1);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
return v___x_311_;
}
else
{
lean_object* v_ref_312_; uint8_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_ref_312_ = lean_ctor_get(v_a_306_, 5);
v___x_313_ = 0;
v___x_314_ = l_Lean_SourceInfo_fromRef(v_ref_312_, v___x_313_);
v___x_315_ = ((lean_object*)(l_Array_tacticArray__get__dec___closed__2));
v___x_316_ = ((lean_object*)(l_Array_tacticArray__get__dec___closed__3));
lean_inc(v___x_314_);
v___x_317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Lean_Syntax_node1(v___x_314_, v___x_315_, v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_a_307_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(v_x_320_, v_a_321_, v_a_322_);
lean_dec_ref(v_a_321_);
return v_res_323_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0));
v___x_339_ = l_String_toRawSubstring_x27(v___x_338_);
return v___x_339_;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13));
v___x_371_ = l_String_toRawSubstring_x27(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(lean_object* v_x_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__1));
v___x_395_ = l_Lean_Syntax_isOfKind(v_x_391_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_box(1);
v___x_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set(v___x_397_, 1, v_a_393_);
return v___x_397_;
}
else
{
lean_object* v_quotContext_398_; lean_object* v_currMacroScope_399_; lean_object* v_ref_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_quotContext_398_ = lean_ctor_get(v_a_392_, 1);
v_currMacroScope_399_ = lean_ctor_get(v_a_392_, 2);
v_ref_400_ = lean_ctor_get(v_a_392_, 5);
v___x_401_ = 0;
v___x_402_ = l_Lean_SourceInfo_fromRef(v_ref_400_, v___x_401_);
v___x_403_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3));
v___x_404_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4));
lean_inc_n(v___x_402_, 61);
v___x_405_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_402_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
v___x_406_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6));
v___x_407_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8));
v___x_408_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9));
v___x_409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_402_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
v___x_410_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11));
v___x_411_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13));
v___x_412_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18));
v___x_413_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19));
v___x_414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_402_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
v___x_415_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20));
v___x_416_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21));
v___x_417_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_402_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
v___x_418_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1);
v___x_419_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3));
lean_inc_n(v_currMacroScope_399_, 5);
lean_inc_n(v_quotContext_398_, 5);
v___x_420_ = l_Lean_addMacroScope(v_quotContext_398_, v___x_419_, v_currMacroScope_399_);
v___x_421_ = lean_box(0);
v___x_422_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5));
v___x_423_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_423_, 0, v___x_402_);
lean_ctor_set(v___x_423_, 1, v___x_418_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
lean_ctor_set(v___x_423_, 3, v___x_422_);
lean_inc_ref(v___x_423_);
lean_inc_ref(v___x_417_);
v___x_424_ = l_Lean_Syntax_node2(v___x_402_, v___x_416_, v___x_417_, v___x_423_);
v___x_425_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52));
v___x_426_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_402_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6));
v___x_428_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7));
v___x_429_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_402_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
v___x_430_ = l_Lean_Syntax_node1(v___x_402_, v___x_428_, v___x_429_);
v___x_431_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8));
v___x_432_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9));
v___x_433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_402_);
lean_ctor_set(v___x_433_, 1, v___x_431_);
v___x_434_ = l_Lean_Syntax_node1(v___x_402_, v___x_432_, v___x_433_);
lean_inc(v___x_430_);
lean_inc_ref(v___x_426_);
v___x_435_ = l_Lean_Syntax_node5(v___x_402_, v___x_406_, v___x_424_, v___x_426_, v___x_430_, v___x_426_, v___x_434_);
v___x_436_ = l_Lean_Syntax_node1(v___x_402_, v___x_411_, v___x_435_);
v___x_437_ = l_Lean_Syntax_node1(v___x_402_, v___x_410_, v___x_436_);
lean_inc_ref(v___x_414_);
v___x_438_ = l_Lean_Syntax_node2(v___x_402_, v___x_412_, v___x_414_, v___x_437_);
v___x_439_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_438_);
v___x_440_ = l_Lean_Syntax_node1(v___x_402_, v___x_411_, v___x_439_);
v___x_441_ = l_Lean_Syntax_node1(v___x_402_, v___x_410_, v___x_440_);
lean_inc_ref(v___x_409_);
v___x_442_ = l_Lean_Syntax_node2(v___x_402_, v___x_407_, v___x_409_, v___x_441_);
v___x_443_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24));
v___x_444_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
v___x_445_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29));
v___x_446_ = l_Lean_addMacroScope(v_quotContext_398_, v___x_445_, v_currMacroScope_399_);
v___x_447_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31));
v___x_448_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_448_, 0, v___x_402_);
lean_ctor_set(v___x_448_, 1, v___x_444_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
lean_ctor_set(v___x_448_, 3, v___x_447_);
v___x_449_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32));
v___x_450_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34));
v___x_451_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16));
v___x_452_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_402_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36));
v___x_454_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_addMacroScope(v_quotContext_398_, v___x_455_, v_currMacroScope_399_);
v___x_457_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41));
v___x_458_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_458_, 0, v___x_402_);
lean_ctor_set(v___x_458_, 1, v___x_454_);
lean_ctor_set(v___x_458_, 2, v___x_456_);
lean_ctor_set(v___x_458_, 3, v___x_457_);
v___x_459_ = l_Lean_Syntax_node1(v___x_402_, v___x_453_, v___x_458_);
v___x_460_ = l_Lean_Syntax_node2(v___x_402_, v___x_450_, v___x_452_, v___x_459_);
v___x_461_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11));
v___x_462_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12));
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_402_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14);
v___x_465_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15));
v___x_466_ = l_Lean_addMacroScope(v_quotContext_398_, v___x_465_, v_currMacroScope_399_);
v___x_467_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_467_, 0, v___x_402_);
lean_ctor_set(v___x_467_, 1, v___x_464_);
lean_ctor_set(v___x_467_, 2, v___x_466_);
lean_ctor_set(v___x_467_, 3, v___x_421_);
lean_inc_ref(v___x_467_);
v___x_468_ = l_Lean_Syntax_node2(v___x_402_, v___x_461_, v___x_463_, v___x_467_);
v___x_469_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_468_);
v___x_470_ = l_Lean_Syntax_node2(v___x_402_, v___x_443_, v___x_423_, v___x_469_);
v___x_471_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51));
v___x_472_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_402_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_Syntax_node3(v___x_402_, v___x_449_, v___x_460_, v___x_470_, v___x_472_);
v___x_474_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_473_);
v___x_475_ = l_Lean_Syntax_node2(v___x_402_, v___x_443_, v___x_448_, v___x_474_);
v___x_476_ = l_Lean_Syntax_node2(v___x_402_, v___x_416_, v___x_417_, v___x_475_);
v___x_477_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
v___x_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_478_, 0, v___x_402_);
lean_ctor_set(v___x_478_, 1, v___x_406_);
lean_ctor_set(v___x_478_, 2, v___x_477_);
v___x_479_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16));
v___x_480_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17));
v___x_481_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_402_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
v___x_482_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19));
v___x_483_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21));
v___x_484_ = l_Lean_Syntax_node1(v___x_402_, v___x_483_, v___x_467_);
lean_inc_ref_n(v___x_478_, 6);
v___x_485_ = l_Lean_Syntax_node2(v___x_402_, v___x_482_, v___x_484_, v___x_478_);
v___x_486_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_485_);
v___x_487_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22));
v___x_488_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_402_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_430_);
v___x_490_ = l_Lean_Syntax_node1(v___x_402_, v___x_411_, v___x_489_);
v___x_491_ = l_Lean_Syntax_node1(v___x_402_, v___x_410_, v___x_490_);
v___x_492_ = l_Lean_Syntax_node4(v___x_402_, v___x_480_, v___x_481_, v___x_486_, v___x_488_, v___x_491_);
v___x_493_ = l_Lean_Syntax_node3(v___x_402_, v___x_406_, v___x_476_, v___x_478_, v___x_492_);
v___x_494_ = l_Lean_Syntax_node1(v___x_402_, v___x_411_, v___x_493_);
v___x_495_ = l_Lean_Syntax_node1(v___x_402_, v___x_410_, v___x_494_);
v___x_496_ = l_Lean_Syntax_node2(v___x_402_, v___x_412_, v___x_414_, v___x_495_);
v___x_497_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53));
v___x_498_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54));
v___x_499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_402_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
v___x_500_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56));
v___x_501_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58));
v___x_502_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60));
v___x_503_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61));
v___x_504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_402_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
v___x_506_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64));
v___x_507_ = l_Lean_addMacroScope(v_quotContext_398_, v___x_506_, v_currMacroScope_399_);
v___x_508_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_508_, 0, v___x_402_);
lean_ctor_set(v___x_508_, 1, v___x_505_);
lean_ctor_set(v___x_508_, 2, v___x_507_);
lean_ctor_set(v___x_508_, 3, v___x_421_);
v___x_509_ = l_Lean_Syntax_node2(v___x_402_, v___x_502_, v___x_504_, v___x_508_);
v___x_510_ = l_Lean_Syntax_node1(v___x_402_, v___x_501_, v___x_509_);
v___x_511_ = l_Lean_Syntax_node1(v___x_402_, v___x_406_, v___x_510_);
v___x_512_ = l_Lean_Syntax_node1(v___x_402_, v___x_500_, v___x_511_);
v___x_513_ = l_Lean_Syntax_node6(v___x_402_, v___x_498_, v___x_499_, v___x_512_, v___x_478_, v___x_478_, v___x_478_, v___x_478_);
v___x_514_ = l_Lean_Syntax_node3(v___x_402_, v___x_406_, v___x_496_, v___x_478_, v___x_513_);
v___x_515_ = l_Lean_Syntax_node1(v___x_402_, v___x_411_, v___x_514_);
v___x_516_ = l_Lean_Syntax_node1(v___x_402_, v___x_410_, v___x_515_);
v___x_517_ = l_Lean_Syntax_node2(v___x_402_, v___x_407_, v___x_409_, v___x_516_);
v___x_518_ = l_Lean_Syntax_node2(v___x_402_, v___x_406_, v___x_442_, v___x_517_);
v___x_519_ = l_Lean_Syntax_node2(v___x_402_, v___x_404_, v___x_405_, v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_a_393_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___boxed(lean_object* v_x_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(v_x_521_, v_a_522_, v_a_523_);
lean_dec_ref(v_a_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_528_ = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_529_ = l_Lean_Syntax_isOfKind(v_x_525_, v___x_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_box(1);
v___x_531_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v_a_527_);
return v___x_531_;
}
else
{
lean_object* v_ref_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_ref_532_ = lean_ctor_get(v_a_526_, 5);
v___x_533_ = 0;
v___x_534_ = l_Lean_SourceInfo_fromRef(v_ref_532_, v___x_533_);
v___x_535_ = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__1));
v___x_536_ = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__2));
lean_inc(v___x_534_);
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_534_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_Syntax_node1(v___x_534_, v___x_535_, v___x_537_);
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_a_527_);
return v___x_539_;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(v_x_540_, v_a_541_, v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_543_;
}
}
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Mem(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Mem(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_MetaTypes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Mem(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_MetaTypes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Mem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Mem(builtin);
}
#ifdef __cplusplus
}
#endif
