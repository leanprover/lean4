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
static const lean_string_object l_Array_tacticArray__get__dec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Array_tacticArray__get__dec___closed__0 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__0_value;
static const lean_string_object l_Array_tacticArray__get__dec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "tacticArray_get_dec"};
static const lean_object* l_Array_tacticArray__get__dec___closed__1 = (const lean_object*)&l_Array_tacticArray__get__dec___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_0),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_1),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value_aux_2),((lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4_value;
static const lean_string_object l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5 = (const lean_object*)&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__5_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
lean_object* l_Array_mkArray0(lean_object*);
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__25));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__37));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__42));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__62));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_mkArray0(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__66));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_tacticArray__get__dec___closed__2));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3));
x_14 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6));
x_17 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8));
x_18 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9));
lean_inc(x_12);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11));
x_21 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13));
x_22 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__15));
x_23 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16));
lean_inc(x_12);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18));
x_26 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19));
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
x_28 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20));
x_29 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21));
lean_inc(x_12);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_12);
lean_ctor_set(x_30, 1, x_28);
x_31 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24));
x_32 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
x_33 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29));
lean_inc(x_9);
lean_inc(x_8);
x_34 = l_Lean_addMacroScope(x_8, x_33, x_9);
x_35 = lean_box(0);
x_36 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31));
lean_inc(x_12);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_37, 3, x_36);
x_38 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32));
x_39 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34));
x_40 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36));
x_41 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
x_42 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_43 = l_Lean_addMacroScope(x_8, x_42, x_9);
x_44 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41));
lean_inc(x_12);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_44);
lean_inc(x_12);
x_46 = l_Lean_Syntax_node1(x_12, x_40, x_45);
lean_inc_ref(x_24);
lean_inc(x_12);
x_47 = l_Lean_Syntax_node2(x_12, x_39, x_24, x_46);
x_48 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__43);
x_49 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__44));
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_addMacroScope(x_8, x_49, x_9);
x_51 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__47));
lean_inc(x_12);
x_52 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_52, 0, x_12);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_50);
lean_ctor_set(x_52, 3, x_51);
x_53 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__49));
x_54 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__50));
lean_inc(x_12);
x_55 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_55, 0, x_12);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_12);
x_56 = l_Lean_Syntax_node1(x_12, x_53, x_55);
lean_inc(x_12);
x_57 = l_Lean_Syntax_node1(x_12, x_16, x_56);
lean_inc(x_57);
lean_inc(x_12);
x_58 = l_Lean_Syntax_node2(x_12, x_31, x_52, x_57);
x_59 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51));
lean_inc(x_12);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_12);
lean_ctor_set(x_60, 1, x_59);
lean_inc_ref(x_60);
lean_inc(x_47);
lean_inc(x_12);
x_61 = l_Lean_Syntax_node3(x_12, x_38, x_47, x_58, x_60);
lean_inc(x_12);
x_62 = l_Lean_Syntax_node1(x_12, x_16, x_61);
lean_inc_ref(x_37);
lean_inc(x_12);
x_63 = l_Lean_Syntax_node2(x_12, x_31, x_37, x_62);
lean_inc_ref(x_30);
lean_inc(x_12);
x_64 = l_Lean_Syntax_node2(x_12, x_29, x_30, x_63);
lean_inc(x_12);
x_65 = l_Lean_Syntax_node1(x_12, x_16, x_64);
lean_inc(x_12);
x_66 = l_Lean_Syntax_node1(x_12, x_21, x_65);
lean_inc(x_12);
x_67 = l_Lean_Syntax_node1(x_12, x_20, x_66);
lean_inc_ref(x_27);
lean_inc(x_12);
x_68 = l_Lean_Syntax_node2(x_12, x_25, x_27, x_67);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_16, x_68);
lean_inc(x_12);
x_70 = l_Lean_Syntax_node1(x_12, x_21, x_69);
lean_inc(x_12);
x_71 = l_Lean_Syntax_node1(x_12, x_20, x_70);
lean_inc_ref(x_60);
lean_inc_ref(x_24);
lean_inc(x_12);
x_72 = l_Lean_Syntax_node3(x_12, x_22, x_24, x_71, x_60);
x_73 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52));
lean_inc(x_12);
x_74 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_74, 0, x_12);
lean_ctor_set(x_74, 1, x_73);
x_75 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53));
x_76 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54));
lean_inc(x_12);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_75);
x_78 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56));
x_79 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58));
x_80 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60));
x_81 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61));
lean_inc(x_12);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
x_84 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64));
lean_inc(x_9);
lean_inc(x_8);
x_85 = l_Lean_addMacroScope(x_8, x_84, x_9);
lean_inc(x_12);
x_86 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_35);
lean_inc(x_12);
x_87 = l_Lean_Syntax_node2(x_12, x_80, x_82, x_86);
lean_inc(x_12);
x_88 = l_Lean_Syntax_node1(x_12, x_79, x_87);
lean_inc(x_12);
x_89 = l_Lean_Syntax_node1(x_12, x_16, x_88);
lean_inc(x_12);
x_90 = l_Lean_Syntax_node1(x_12, x_78, x_89);
x_91 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
lean_inc(x_12);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_12);
lean_ctor_set(x_92, 1, x_16);
lean_ctor_set(x_92, 2, x_91);
lean_inc_ref_n(x_92, 3);
lean_inc(x_12);
x_93 = l_Lean_Syntax_node6(x_12, x_76, x_77, x_90, x_92, x_92, x_92, x_92);
lean_inc(x_93);
lean_inc_ref(x_74);
lean_inc(x_12);
x_94 = l_Lean_Syntax_node3(x_12, x_16, x_72, x_74, x_93);
lean_inc(x_12);
x_95 = l_Lean_Syntax_node1(x_12, x_21, x_94);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node1(x_12, x_20, x_95);
lean_inc_ref(x_19);
lean_inc(x_12);
x_97 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_96);
x_98 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__67);
x_99 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__68));
x_100 = l_Lean_addMacroScope(x_8, x_99, x_9);
x_101 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__71));
lean_inc(x_12);
x_102 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_102, 0, x_12);
lean_ctor_set(x_102, 1, x_98);
lean_ctor_set(x_102, 2, x_100);
lean_ctor_set(x_102, 3, x_101);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node2(x_12, x_31, x_102, x_57);
lean_inc_ref(x_60);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node3(x_12, x_38, x_47, x_103, x_60);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node1(x_12, x_16, x_104);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node2(x_12, x_31, x_37, x_105);
lean_inc(x_12);
x_107 = l_Lean_Syntax_node2(x_12, x_29, x_30, x_106);
lean_inc(x_12);
x_108 = l_Lean_Syntax_node1(x_12, x_16, x_107);
lean_inc(x_12);
x_109 = l_Lean_Syntax_node1(x_12, x_21, x_108);
lean_inc(x_12);
x_110 = l_Lean_Syntax_node1(x_12, x_20, x_109);
lean_inc(x_12);
x_111 = l_Lean_Syntax_node2(x_12, x_25, x_27, x_110);
lean_inc(x_12);
x_112 = l_Lean_Syntax_node1(x_12, x_16, x_111);
lean_inc(x_12);
x_113 = l_Lean_Syntax_node1(x_12, x_21, x_112);
lean_inc(x_12);
x_114 = l_Lean_Syntax_node1(x_12, x_20, x_113);
lean_inc(x_12);
x_115 = l_Lean_Syntax_node3(x_12, x_22, x_24, x_114, x_60);
lean_inc(x_12);
x_116 = l_Lean_Syntax_node3(x_12, x_16, x_115, x_74, x_93);
lean_inc(x_12);
x_117 = l_Lean_Syntax_node1(x_12, x_21, x_116);
lean_inc(x_12);
x_118 = l_Lean_Syntax_node1(x_12, x_20, x_117);
lean_inc(x_12);
x_119 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_118);
lean_inc(x_12);
x_120 = l_Lean_Syntax_node2(x_12, x_16, x_97, x_119);
x_121 = l_Lean_Syntax_node2(x_12, x_14, x_15, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_3);
return x_122;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l_Array_tacticArray__get__dec___closed__2));
x_12 = ((lean_object*)(l_Array_tacticArray__get__dec___closed__3));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Syntax_node1(x_10, x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__0));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__13));
x_2 = l_String_toRawSubstring_x27(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_2);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = 0;
x_12 = l_Lean_SourceInfo_fromRef(x_10, x_11);
lean_dec(x_10);
x_13 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__3));
x_14 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__4));
lean_inc(x_12);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
x_16 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__6));
x_17 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__8));
x_18 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__9));
lean_inc(x_12);
x_19 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__11));
x_21 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__13));
x_22 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__18));
x_23 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__19));
lean_inc(x_12);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__20));
x_26 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__21));
lean_inc(x_12);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__1);
x_29 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__3));
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_addMacroScope(x_8, x_29, x_9);
x_31 = lean_box(0);
x_32 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__5));
lean_inc(x_12);
x_33 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
lean_inc_ref(x_33);
lean_inc_ref(x_27);
lean_inc(x_12);
x_34 = l_Lean_Syntax_node2(x_12, x_26, x_27, x_33);
x_35 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__52));
lean_inc(x_12);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
x_37 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__6));
x_38 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__7));
lean_inc(x_12);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_37);
lean_inc(x_12);
x_40 = l_Lean_Syntax_node1(x_12, x_38, x_39);
x_41 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__8));
x_42 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__9));
lean_inc(x_12);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_41);
lean_inc(x_12);
x_44 = l_Lean_Syntax_node1(x_12, x_42, x_43);
lean_inc(x_40);
lean_inc_ref(x_36);
lean_inc(x_12);
x_45 = l_Lean_Syntax_node5(x_12, x_16, x_34, x_36, x_40, x_36, x_44);
lean_inc(x_12);
x_46 = l_Lean_Syntax_node1(x_12, x_21, x_45);
lean_inc(x_12);
x_47 = l_Lean_Syntax_node1(x_12, x_20, x_46);
lean_inc_ref(x_24);
lean_inc(x_12);
x_48 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_47);
lean_inc(x_12);
x_49 = l_Lean_Syntax_node1(x_12, x_16, x_48);
lean_inc(x_12);
x_50 = l_Lean_Syntax_node1(x_12, x_21, x_49);
lean_inc(x_12);
x_51 = l_Lean_Syntax_node1(x_12, x_20, x_50);
lean_inc_ref(x_19);
lean_inc(x_12);
x_52 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_51);
x_53 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__24));
x_54 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__26);
x_55 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__29));
lean_inc(x_9);
lean_inc(x_8);
x_56 = l_Lean_addMacroScope(x_8, x_55, x_9);
x_57 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__31));
lean_inc(x_12);
x_58 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__32));
x_60 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__34));
x_61 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__16));
lean_inc(x_12);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_12);
lean_ctor_set(x_62, 1, x_61);
x_63 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__36));
x_64 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__38);
x_65 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_66 = l_Lean_addMacroScope(x_8, x_65, x_9);
x_67 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__41));
lean_inc(x_12);
x_68 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_68, 0, x_12);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_66);
lean_ctor_set(x_68, 3, x_67);
lean_inc(x_12);
x_69 = l_Lean_Syntax_node1(x_12, x_63, x_68);
lean_inc(x_12);
x_70 = l_Lean_Syntax_node2(x_12, x_60, x_62, x_69);
x_71 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__11));
x_72 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__12));
lean_inc(x_12);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_12);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__14);
x_75 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__15));
lean_inc(x_9);
lean_inc(x_8);
x_76 = l_Lean_addMacroScope(x_8, x_75, x_9);
lean_inc(x_12);
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_12);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_31);
lean_inc_ref(x_77);
lean_inc(x_12);
x_78 = l_Lean_Syntax_node2(x_12, x_71, x_73, x_77);
lean_inc(x_12);
x_79 = l_Lean_Syntax_node1(x_12, x_16, x_78);
lean_inc(x_12);
x_80 = l_Lean_Syntax_node2(x_12, x_53, x_33, x_79);
x_81 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__51));
lean_inc(x_12);
x_82 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_82, 0, x_12);
lean_ctor_set(x_82, 1, x_81);
lean_inc(x_12);
x_83 = l_Lean_Syntax_node3(x_12, x_59, x_70, x_80, x_82);
lean_inc(x_12);
x_84 = l_Lean_Syntax_node1(x_12, x_16, x_83);
lean_inc(x_12);
x_85 = l_Lean_Syntax_node2(x_12, x_53, x_58, x_84);
lean_inc(x_12);
x_86 = l_Lean_Syntax_node2(x_12, x_26, x_27, x_85);
x_87 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__65);
lean_inc(x_12);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_12);
lean_ctor_set(x_88, 1, x_16);
lean_ctor_set(x_88, 2, x_87);
x_89 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__16));
x_90 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__17));
lean_inc(x_12);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_12);
lean_ctor_set(x_91, 1, x_89);
x_92 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__19));
x_93 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__21));
lean_inc(x_12);
x_94 = l_Lean_Syntax_node1(x_12, x_93, x_77);
lean_inc_ref(x_88);
lean_inc(x_12);
x_95 = l_Lean_Syntax_node2(x_12, x_92, x_94, x_88);
lean_inc(x_12);
x_96 = l_Lean_Syntax_node1(x_12, x_16, x_95);
x_97 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__mem__dec__1___closed__22));
lean_inc(x_12);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_12);
lean_ctor_set(x_98, 1, x_97);
lean_inc(x_12);
x_99 = l_Lean_Syntax_node1(x_12, x_16, x_40);
lean_inc(x_12);
x_100 = l_Lean_Syntax_node1(x_12, x_21, x_99);
lean_inc(x_12);
x_101 = l_Lean_Syntax_node1(x_12, x_20, x_100);
lean_inc(x_12);
x_102 = l_Lean_Syntax_node4(x_12, x_90, x_91, x_96, x_98, x_101);
lean_inc_ref(x_88);
lean_inc(x_12);
x_103 = l_Lean_Syntax_node3(x_12, x_16, x_86, x_88, x_102);
lean_inc(x_12);
x_104 = l_Lean_Syntax_node1(x_12, x_21, x_103);
lean_inc(x_12);
x_105 = l_Lean_Syntax_node1(x_12, x_20, x_104);
lean_inc(x_12);
x_106 = l_Lean_Syntax_node2(x_12, x_22, x_24, x_105);
x_107 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__53));
x_108 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__54));
lean_inc(x_12);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_12);
lean_ctor_set(x_109, 1, x_107);
x_110 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__56));
x_111 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__58));
x_112 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__60));
x_113 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__61));
lean_inc(x_12);
x_114 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_114, 0, x_12);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_obj_once(&l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63, &l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63_once, _init_l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__63);
x_116 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__Array__tacticArray__get__dec__1___closed__64));
x_117 = l_Lean_addMacroScope(x_8, x_116, x_9);
lean_inc(x_12);
x_118 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_118, 0, x_12);
lean_ctor_set(x_118, 1, x_115);
lean_ctor_set(x_118, 2, x_117);
lean_ctor_set(x_118, 3, x_31);
lean_inc(x_12);
x_119 = l_Lean_Syntax_node2(x_12, x_112, x_114, x_118);
lean_inc(x_12);
x_120 = l_Lean_Syntax_node1(x_12, x_111, x_119);
lean_inc(x_12);
x_121 = l_Lean_Syntax_node1(x_12, x_16, x_120);
lean_inc(x_12);
x_122 = l_Lean_Syntax_node1(x_12, x_110, x_121);
lean_inc_ref_n(x_88, 4);
lean_inc(x_12);
x_123 = l_Lean_Syntax_node6(x_12, x_108, x_109, x_122, x_88, x_88, x_88, x_88);
lean_inc(x_12);
x_124 = l_Lean_Syntax_node3(x_12, x_16, x_106, x_88, x_123);
lean_inc(x_12);
x_125 = l_Lean_Syntax_node1(x_12, x_21, x_124);
lean_inc(x_12);
x_126 = l_Lean_Syntax_node1(x_12, x_20, x_125);
lean_inc(x_12);
x_127 = l_Lean_Syntax_node2(x_12, x_17, x_19, x_126);
lean_inc(x_12);
x_128 = l_Lean_Syntax_node2(x_12, x_16, x_52, x_127);
x_129 = l_Lean_Syntax_node2(x_12, x_14, x_15, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_3);
return x_130;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__1___closed__1));
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 5);
x_9 = 0;
x_10 = l_Lean_SourceInfo_fromRef(x_8, x_9);
x_11 = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__1));
x_12 = ((lean_object*)(l_Array_tacticArray__mem__dec___closed__2));
lean_inc(x_10);
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Syntax_node1(x_10, x_11, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array___aux__Init__Data__Array__Mem______macroRules__tacticDecreasing__trivial__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
